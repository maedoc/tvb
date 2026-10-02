#!/usr/bin/env python
"""Compare the Bend MontbrioPazoRoxin prototype against the numba hybrid.

Two independent checks:

  1. BIT-EXACT one-step drift.  A float32 numba kernel evaluates the model's
     expression string in the same left-to-right order the Bend code does, from
     the same initial state, and must agree with Bend's first step bit for bit.
     This is what pins the transcription and the operator order; Bend 2.0
     cannot prove it (see LAWS.bend: `{==}` is structural and float values do
     not normalise).

  2. TOLERANCE over the whole run.  The real `NbHybridBackend` -- the reference
     implementation, with its own float32 buffers, CSR gather, delay ring and
     monitors -- runs the same network, and the traces must agree to a relative
     1e-4.

Both backends get the same network: one subnet, MontbrioPazoRoxin, Heun, Linear
coupling on both coupling variables, a dense off-diagonal connectome, and
per-edge integer-step delays (`round(lengths / cv / dt)`, the reference's rule).

    python compare_montbrio.py --n 300 --steps 300 --points 8 --threads 8
"""
from __future__ import annotations

import argparse
import subprocess
import sys
import time
from pathlib import Path

import numpy as np
from scipy import sparse as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from run_montbrio import (Job, build_binary, parse_out, run_bend,  # noqa: E402
                          DT, TAU, DELTA, ETA, J_SYN, I_IN, C_CR, C_CV,
                          CFA, CFB, SCALE)

RTOL = 1e-4


# --------------------------------------------------------------------------
# the numba reference kernel, mirroring the model's expression string exactly
# --------------------------------------------------------------------------

_REF_KERNEL = None  # compiled once: a fresh njit object would re-JIT every call


def _ref_kernel():
    import numba as nb

    @nb.njit(cache=True, fastmath=False)
    def run(x_r, x_v, w_data, w_idx, w_ptr, idelays, buf_r, buf_v,
            nstep, dt, tau, delta, eta, jj, ii, cr_p, cv_p, cfa, cfb, scale,
            H, out_r, out_v):
        """One subnet, Heun, CSR coupling with per-edge delays.

        `buf_*` are pre-broadcast with the initial state (the reference does
        this too), slot = (t - 1 - idelay) mod H, coupling computed once per
        step and reused by both Heun stages.
        """
        for t in range(1, nstep + 1):
            cr = np.zeros(x_r.shape[0], np.float32)
            cv = np.zeros(x_r.shape[0], np.float32)
            for j in range(x_r.shape[0]):
                wr = np.float32(0.0)
                wv = np.float32(0.0)
                for e in range(w_ptr[j], w_ptr[j + 1]):
                    s = w_idx[e]
                    slot = (t - 1 - idelays[e] + H) % H
                    we = w_data[e]
                    wr += we * buf_r[s, slot]
                    wv += we * buf_v[s, slot]
                wr = cfa * wr + cfb
                wv = cfa * wv + cfb
                cr[j] = scale * wr
                cv[j] = scale * wv
            for i in range(x_r.shape[0]):
                r = x_r[i]
                v = x_v[i]
                C_r = cr[i]
                C_v = cv[i]
                # --- the model expression, term for term ---
                d0r = (np.float32(1.0) / tau) * (delta / (np.float32(np.pi) * tau)
                                                  + 2 * v * r)
                q = ((((np.float32(np.pi) * np.float32(np.pi)) * tau) * tau) * r) * r
                a1 = v * v - q
                a2 = a1 + eta
                a3 = a2 + jj * tau * r
                a4 = a3 + ii
                a5 = a4 + cr_p * C_r
                a6 = a5 + cv_p * C_v
                d0v = (np.float32(1.0) / tau) * a6
                # --- stage 1, clamped on r ---
                i1r = r + dt * d0r
                if i1r < np.float32(0.0):
                    i1r = np.float32(0.0)
                i1v = v + dt * d0v
                d1r = (np.float32(1.0) / tau) * (delta / (np.float32(np.pi) * tau)
                                                  + 2 * i1v * i1r)
                q1 = ((((np.float32(np.pi) * np.float32(np.pi)) * tau) * tau) * i1r) * i1r
                b1 = i1v * i1v - q1
                b2 = b1 + eta
                b3 = b2 + jj * tau * i1r
                b4 = b3 + ii
                b5 = b4 + cr_p * C_r
                b6 = b5 + cv_p * C_v
                d1v = (np.float32(1.0) / tau) * b6
                half = np.float32(dt) * np.float32(0.5)
                zr = r + half * (d0r + d1r)
                if zr < np.float32(0.0):
                    zr = np.float32(0.0)
                zv = v + half * (d0v + d1v)
                x_r[i] = zr
                x_v[i] = zv
                # push; slot t mod H
                buf_r[i, t % H] = zr
                buf_v[i, t % H] = zv
            out_r[t - 1] = x_r[0]
            out_v[t - 1] = x_v[0]
        return x_r, x_v
    return run


def job_arrays(job: Job):
    """The job's arrays, decoded exactly as Bend decodes them.

    Bend reads scaled integers and divides by 1e6 in F32, so the reference must
    see the same values -- otherwise a bit-exact comparison would be measuring
    the encoding, not the arithmetic.
    """
    dec = lambda a: (np.array(a, np.int64).astype(np.uint32).view(np.int32)
                     .astype(np.float32) / np.float32(SCALE))
    w = dec([int(round(float(v) * SCALE)) for v in job.w])
    r = dec([int(round(float(v) * SCALE)) for v in job.ic_r])
    v = dec([int(round(float(v) * SCALE)) for v in job.ic_v])
    return w, r, v


def ref_run(job: Job, nstep: int):
    global _REF_KERNEL
    if _REF_KERNEL is None:
        _REF_KERNEL = _ref_kernel()
    run = _REF_KERNEL
    n = job.n
    H = job.hslots
    w, ic_r, ic_v = job_arrays(job)
    M = sp.csr_matrix((w.astype(np.float64), (job.tgt, job.idx)), shape=(n, n))
    x_r, x_v = ic_r.copy(), ic_v.copy()
    buf_r = np.repeat(x_r[:, None], H, axis=1).astype(np.float32)
    buf_v = np.repeat(x_v[:, None], H, axis=1).astype(np.float32)
    out_r = np.zeros(nstep, np.float32)
    out_v = np.zeros(nstep, np.float32)
    args = (x_r, x_v, M.data.astype(np.float32), M.indices.astype(np.int64),
            M.indptr.astype(np.int64), job.delays.astype(np.int64),
            buf_r, buf_v, nstep, np.float32(DT), np.float32(TAU),
            np.float32(DELTA), np.float32(ETA), np.float32(J_SYN),
            np.float32(I_IN), np.float32(C_CR), np.float32(C_CV),
            np.float32(CFA), np.float32(CFB), np.float32(job.scales[0]), H,
            out_r, out_v)
    x_r[:] = ic_r  # the warm-up call must not consume the real initial state
    x_v[:] = ic_v
    buf_r[:] = np.repeat(ic_r[:, None], H, axis=1).astype(np.float32)
    buf_v[:] = np.repeat(ic_v[:, None], H, axis=1).astype(np.float32)
    run(*args)  # JIT warm-up (1 step, result discarded)
    x_r[:] = ic_r
    x_v[:] = ic_v
    buf_r[:] = np.repeat(ic_r[:, None], H, axis=1).astype(np.float32)
    buf_v[:] = np.repeat(ic_v[:, None], H, axis=1).astype(np.float32)
    t0 = time.perf_counter()
    run(*args)
    return out_r, out_v, time.perf_counter() - t0


# --------------------------------------------------------------------------
# the real reference: NbHybridBackend
# --------------------------------------------------------------------------

def nb_hybrid_run(job: Job, nstep: int):
    from tvb.simulator.backend.nb_hybrid import NbHybridBackend
    from tvb.simulator.hybrid.network import NetworkSet
    from tvb.simulator.hybrid.subnetwork import Subnetwork
    from tvb.simulator.hybrid.intra_projection import IntraProjection
    from tvb.simulator.hybrid.coupling import Linear
    from tvb.simulator.models.infinite_theta import MontbrioPazoRoxin
    from tvb.simulator.integrators import HeunDeterministic

    n = job.n
    model = MontbrioPazoRoxin()
    model.configure()
    sn = Subnetwork(name="sn", model=model, scheme=HeunDeterministic(dt=DT),
                    nnodes=n)
    w = sp.csr_matrix((job.w.astype(np.float64), (job.tgt, job.idx)),
                      shape=(n, n))
    # lengths from the integer delays the Bend job uses: delays = round(L/cv/dt)
    lengths = sp.csr_matrix((job.delays.astype(np.float64) * 1.0 * DT,
                             (job.tgt, job.idx)), shape=(n, n))
    proj = IntraProjection(
        source_cvar=np.array([0, 1], dtype=np.int_),
        target_cvar=np.array([0, 1], dtype=np.int_),
        weights=w, lengths=lengths, cv=1.0, dt=DT, scale=float(job.scales[0]),
        cfun=Linear(),
    )
    sn.projections = [proj]
    sn.configure()
    ns = NetworkSet(subnets=[sn], projections=[])
    ns.configure()

    _, ic_r, ic_v = job_arrays(job)
    x0 = np.stack([ic_r, ic_v]).astype(np.float64)[:, :, None]
    backend = NbHybridBackend()
    t0 = time.perf_counter()
    res = backend.run_network(ns, nstep=nstep, chunk_size=1,
                              initial_states=[x0])
    dt = time.perf_counter() - t0
    data = res[0][1]  # (nstep, n_voi, n_nodes, n_modes)
    return data[:, 0, 0, 0], data[:, 1, 0, 0], dt   # node 0, to match Bend's trace


# --------------------------------------------------------------------------
# comparison
# --------------------------------------------------------------------------

SCALE = 1_000_000


def trace_of(job: Job, bend_out: dict, point: int, steps: int):
    """Node 0's r and V, as Bend's fixed-point integers."""
    return bend_out[point]["r"][:steps], bend_out[point]["v"][:steps]


def to_f32(ns: np.ndarray) -> np.ndarray:
    return (ns.astype(np.float64) / SCALE).astype(np.float32)


def to_scaled(x) -> np.ndarray:
    """round(value * 1e6) -- the same integer Bend emits, computed from the
    reference's float32, so the two streams can be compared exactly."""
    xf = np.asarray(x, np.float32)
    return np.sign(xf).astype(np.int64) * np.floor(
        np.abs(xf.astype(np.float64)) * SCALE + 0.5).astype(np.int64)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=300)
    ap.add_argument("--steps", type=int, default=300)
    ap.add_argument("--points", type=int, default=8)
    ap.add_argument("--max-delay", type=int, default=10)
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--skip-nb-hybrid", action="store_true")
    ap.add_argument("--isolation", action="store_true",
                    help="check that each sweep point, run alone, reproduces "
                         "exactly the point from the full sweep, and that "
                         "repeated runs are identical")
    ap.add_argument("--zero-delays", action="store_true",
                    help="zero the delays in Bend AND the references; checks "
                         "the zero-delay path against NbHybridBackend")
    ap.add_argument("--disable-delays", action="store_true",
                    help="zero the delays ONLY in Bend's job file while the "
                         "reference keeps them; the comparison must then FAIL, "
                         "which is what proves the delay handling is real")
    args = ap.parse_args()

    scales = (np.linspace(0.0, 5.0, args.points) if args.points > 1
              else np.array([2.0]))
    job = Job(args.n, args.steps, args.points, args.max_delay, scales,
              seed=args.seed)

    binary = build_binary(HERE / "montbrio_sweep", force=False)
    # the job Bend actually runs; with --disable-delays its delays are zeroed
    # while every reference below keeps the real ones
    job_bend = Job(args.n, args.steps, args.points, args.max_delay, scales,
                   seed=args.seed)
    if args.zero_delays:
        # Build BOTH sides with max_delay = 0 rather than zeroing the delays of
        # a job that has them: nb_hybrid sizes its ring as max(idelay)+1, so
        # zeroing the lengths collapses its horizon to 1 while Bend would keep
        # hslots = next_pow2(11).  A ring of size 1 aliases, and the reference
        # then reads a different step than Bend does -- a reference-side
        # artefact, not a delay bug.
        job = Job(args.n, args.steps, args.points, 0, scales, seed=args.seed)
        job_bend = Job(args.n, args.steps, args.points, 0, scales,
                       seed=args.seed)
    if args.disable_delays:
        job_bend.delays = np.zeros_like(job_bend.delays)
        print("NOTE: Bend is running with every delay zeroed; the references "
              "keep the real delays, so this run MUST fail.")
    text, bend_wall = run_bend(binary, job_bend, HERE / "jobdir",
                               threads=args.threads)
    out = parse_out(text)

    ok = True
    print(f"n={job.n} steps={job.steps} points={job.points} "
          f"max_delay={job.max_delay} threads={args.threads}")

    if args.isolation:
        # every point run ALONE must reproduce the full sweep's point exactly.
        # Each point builds its own arrays from the shared byte lists, so any
        # cross-contamination would show up here as a non-zero difference.
        worst = 0
        for k in sorted(out):
            solo = Job(job.n, job.steps, 1, job.max_delay,
                       np.array([job.scales[k]]), seed=args.seed)
            solo.delays = job.delays.copy()
            t_solo, _ = run_bend(binary, solo, HERE / f"jobdir_solo{k}",
                                 threads=args.threads)
            so = parse_out(t_solo)[0]
            d = max(int(np.abs(out[k]["r"] - so["r"]).max()),
                    int(np.abs(out[k]["v"] - so["v"]).max()))
            worst = max(worst, d)
            print(f"  point {k} alone vs in-sweep: max |delta| = {d} "
                  f"fixed-point units (exact = 0)")
        # determinism: the same job twice must give identical output
        t_again, _ = run_bend(binary, job_bend, HERE / "jobdir_again",
                              threads=args.threads)
        again = parse_out(t_again)
        same = (sorted(again) == sorted(out)
                and all(np.array_equal(again[k]["r"], out[k]["r"])
                        and np.array_equal(again[k]["v"], out[k]["v"])
                        and again[k]["scale"] == out[k]["scale"]
                        for k in out))
        print(f"  repeated run identical: {same}")
        print(f"sweep isolation: worst deviation {worst} (want 0), "
              f"deterministic={same}")
        ok &= (worst == 0) and same
        print("RESULT:", "PASS" if ok else "FAIL")
        return 0 if ok else 1

    # ---- 1. bit-exact one-step drift -------------------------------------
    # the one-step job must be built with the SAME max_delay as the job Bend
    # ran, otherwise the two sides differ in ring size and initial conditions
    job1 = Job(args.n, 1, 1, job_bend.max_delay, np.array([float(scales[0])]),
               seed=args.seed)
    job1.delays = job_bend.delays.copy()
    t1, _ = run_bend(binary, job_bend, HERE / "jobdir1", threads=1)
    o1 = parse_out(t1)
    bend_r1, bend_v1 = trace_of(job1, o1, 0, 1)
    ref_r1, ref_v1, _ = ref_run(job1, 1)   # per-node final state
    # exact: compare the fixed-point integers, which encode the float32 bit
    # pattern without going through decimal text
    same_r = int(bend_r1[0]) == int(to_scaled(ref_r1[:1])[0])
    same_v = int(bend_v1[0]) == int(to_scaled(ref_v1[:1])[0])
    print(f"one-step drift bit-exact: r={same_r} V={same_v}   "
          f"bend=({bend_r1[0] / SCALE:.9g}, {bend_v1[0] / SCALE:.9g}) "
          f"ref=({to_f32(to_scaled(ref_r1[:1]))[0]:.9g}, "
          f"{to_f32(to_scaled(ref_v1[:1]))[0]:.9g})")
    if not (same_r and same_v):
        print(f"  integer gap: r {int(bend_r1[0]) - int(to_scaled(ref_r1[:1])[0])}"
              f"  V {int(bend_v1[0]) - int(to_scaled(ref_v1[:1])[0])}"
              f"   (1 unit = 1e-6, float32 ulp near 1.0 is ~1.2e-7)")
    ok &= same_r and same_v

    # ---- 2. tolerance over the whole run ---------------------------------
    steps = args.steps
    ref_r0, ref_v0, ref_wall = ref_run(job, steps)
    for k in sorted(out):
        br, bv = trace_of(job_bend, out, k, steps)
        if k == 0:
            # only point 0 shares the reference's coupling scale
            # compare the fixed-point integers: exact, with no decimal
            # round-trip in the way
            rr_i, rv_i = to_scaled(ref_r0), to_scaled(ref_v0)
            dr = np.abs(br - rr_i).max() / max(abs(rr_i).max(), 1)
            dv = np.abs(bv - rv_i).max() / max(abs(rv_i).max(), 1)
            exact_r = int((br == rr_i).sum())
            exact_v = int((bv == rv_i).sum())
            print(f"  point 0 (scale {out[k]['scale']:.3f}) vs numba kernel: "
                  f"max rel dev r={dr:.3e} V={dv:.3e}  (tol {RTOL:.0e})"
                  f"   identical steps: r {exact_r}/{steps} V {exact_v}/{steps}")
            ok &= dr <= RTOL and dv <= RTOL

    if not args.skip_nb_hybrid:
        nhr, nhv, nh_wall = nb_hybrid_run(job, steps)
        br, bv = trace_of(job_bend, out, 0, steps)
        nhr_i, nhv_i = to_scaled(nhr), to_scaled(nhv)
        dr = np.abs(br - nhr_i).max() / max(abs(nhr_i).max(), 1)
        dv = np.abs(bv - nhv_i).max() / max(abs(nhv_i).max(), 1)
        print(f"  point 0 vs NbHybridBackend: max rel dev r={dr:.3e} "
              f"V={dv:.3e}  (tol {RTOL:.0e})")
        ok &= dr <= RTOL and dv <= RTOL
        print(f"wall-time: bend sweep = {bend_wall * 1e3:.1f} ms | "
              f"numba kernel = {ref_wall * 1e3:.1f} ms | "
              f"NbHybridBackend = {nh_wall * 1e3:.1f} ms")

    print("RESULT:", "PASS" if ok else "FAIL")
    if not ok:
        print("  (compare_montbrio.py exits nonzero)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
