#!/usr/bin/env python
"""Driver for the Bend MontbrioPazoRoxin sweep prototype.

Writes the job files the Bend CLI reads, runs the compiled binary, parses its
output, and (optionally) compares against the numba hybrid.

    python run_montbrio.py --n 300 --steps 300 --points 8 --threads 8
    python run_montbrio.py --n 20 --steps 2 --points 1          # smoke test
"""
from __future__ import annotations

import argparse
import os
import struct
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
BEND = os.environ.get("BEND", "/home/duke/.bend/bin/bend")
SCALE = 1_000_000  # floats travel as scaled u32 (Bend has no float bitcast)

# MontbrioPazoRoxin defaults (models/infinite_theta.py)
DT, TAU, DELTA, ETA, J_SYN, I_IN = 0.1, 1.0, 1.0, -5.0, 15.0, 0.0
# the model's coupling weights.  These are MontbrioPazoRoxin's own defaults
# (models/infinite_theta.py): the incoming coupling enters through the rate
# variable only.  Getting cv wrong is silent -- the run still looks plausible --
# so the values are pinned here and checked against the generated numba kernel.
C_CR, C_CV = 1.0, 0.0
CFA, CFB = 1.0, 0.0            # Linear coupling cfun: a*wsum + b


def s32(x: float) -> int:
    """Encode a float as a signed fixed-point integer (u32 two's complement)."""
    return int(np.int32(round(float(x) * SCALE))) & 0xFFFFFFFF


def u32(x) -> int:
    return int(x) & 0xFFFFFFFF


def ceil_log2(n: int) -> int:
    d = 0
    while (1 << d) < n:
        d += 1
    return d


class Job:
    """The job the Bend CLI consumes."""

    def __init__(self, n, steps, points, max_delay, scales, seed=0, weight=0.01):
        rng = np.random.RandomState(seed)
        self.n, self.steps, self.points = n, steps, points
        self.max_delay = max_delay
        self.hslots = 1 << ceil_log2(max_delay + 1)
        self.scales = np.asarray(scales, np.float32)

        rows = np.repeat(np.arange(n), n)
        cols = np.tile(np.arange(n), n)
        keep = rows != cols
        rows, cols = rows[keep], cols[keep]
        self.nnz = rows.size
        self.idx = cols.astype(np.int64)
        self.tgt = rows.astype(np.int64)
        self.w = np.full(self.nnz, weight, np.float64)
        self.delays = rng.randint(0, max_delay + 1, self.nnz).astype(np.int64)

        self.ic_r = np.abs(rng.uniform(0.0, 0.2, n)).astype(np.float32)
        self.ic_v = rng.uniform(-1.0, -0.5, n).astype(np.float32)

    def write(self, d: Path) -> list[str]:
        d.mkdir(parents=True, exist_ok=True)
        ne = self.nnz + 1  # one sentinel edge flushes the last CSR row

        # edge: idx (low 16) | delay (high 16); the sentinel reads (0, 0)
        edge = np.empty(ne, np.uint32)
        edge[: self.nnz] = (self.idx & 0xFFFF) | ((self.delays & 0xFFFF) << 16)
        edge[self.nnz] = 0
        # target: sentinel points one past the last node so the flat loop flushes
        tgt = np.empty(ne, np.uint32)
        tgt[: self.nnz] = self.tgt
        tgt[self.nnz] = self.n

        w = np.empty(ne, np.uint32)
        w[: self.nnz] = [s32(v) for v in self.w]
        w[self.nnz] = 0

        # history is pre-broadcast: the reference fills every horizon slot with
        # the initial state, so a delayed read before t <= max_delay sees the IC
        hist_r = np.repeat(self.ic_r[:, None], self.hslots, axis=1).reshape(-1)
        hist_v = np.repeat(self.ic_v[:, None], self.hslots, axis=1).reshape(-1)

        files = {
            "JOB_SWEEP": np.array([s32(s) for s in self.scales], np.uint32),
            "JOB_ICR": np.array([s32(v) for v in self.ic_r], np.uint32),
            "JOB_ICV": np.array([s32(v) for v in self.ic_v], np.uint32),
            "JOB_HISTR": np.array([s32(v) for v in hist_r], np.uint32),
            "JOB_HISTV": np.array([s32(v) for v in hist_v], np.uint32),
            "JOB_EDGE": edge,
            "JOB_TGT": tgt,
            "JOB_W": w,
        }
        for name, arr in files.items():
            arr.tofile(d / (name.lower() + ".bin"))
        return [str(d / (k.lower() + ".bin")) for k in files]

    def header(self) -> list[str]:
        return [
            str(u32(self.n)), str(u32(self.steps)), str(u32(self.points)),
            str(ceil_log2(self.n + 1)),                 # state array depth
            str(ceil_log2(self.n * self.hslots)),       # history array depth
            str(ceil_log2(2 * self.steps)),            # trace array depth
            str(u32(self.hslots)), str(u32(self.nnz)),
            str(ceil_log2(self.nnz + 1)),               # edge array depth
            str(u32(SCALE)),
            str(s32(DT)), str(s32(TAU)), str(s32(DELTA)), str(s32(ETA)),
            str(s32(J_SYN)), str(s32(I_IN)), str(s32(C_CR)), str(s32(C_CV)),
            str(s32(CFA)), str(s32(CFB)),
            "0",                                         # reserved
            str(u32(self.idx[0])), str(u32(self.delays[0])),
        ]


def build_binary(out: Path, force: bool = False) -> Path:
    if out.exists() and not force:
        return out
    src = HERE / "montbrio_sweep.bend"
    print(f"building {out} ...", flush=True)
    r = subprocess.run([BEND, str(src), "-o", str(out)], capture_output=True, text=True)
    if r.returncode != 0 or not out.exists():
        sys.stderr.write(r.stdout + r.stderr)
        raise SystemExit("bend build failed")
    return out


def run_bend(binary: Path, job: Job, jobdir: Path, threads: int = 1,
             env_extra: dict | None = None) -> tuple[str, float]:
    job.write(jobdir)
    hdr = job.header()
    paths = job.write(jobdir)  # idempotent; keeps the file list authoritative
    env = dict(os.environ)
    env.update({
        "JOB_SWEEP": paths[0], "JOB_ICR": paths[1], "JOB_ICV": paths[2],
        "JOB_HISTR": paths[3], "JOB_HISTV": paths[4],
        "JOB_EDGE": paths[5], "JOB_TGT": paths[6], "JOB_W": paths[7],
    })
    if env_extra:
        env.update(env_extra)
    cmd = [str(binary), "--threads", str(threads), "--gpu", "off"] + hdr
    t0 = time.perf_counter()
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    dt = time.perf_counter() - t0
    if r.returncode != 0:
        sys.stderr.write(f"bend run failed ({r.returncode}):\n{r.stdout}\n{r.stderr}\n")
        raise SystemExit(2)
    return r.stdout, dt


SCALE = 1_000_000  # matches Bend's fixed-point trace channel


def parse_out(text: str) -> dict[int, dict]:
    """Parse the per-point blocks.

    Bend emits round(value * 1e6) as an integer, not a decimal: F32.show is not
    round-trip exact, so a text float can land an ulp away from the value that
    was actually computed.  Keeping the integers makes the comparison exact --
    two implementations that agree bit for bit emit the same integers.
    """
    out = {}
    cur = None
    for line in text.splitlines():
        if line.startswith("POINT "):
            _, k, _, scale = line.split()
            cur = int(k)
            out[cur] = {"scale": int(scale) / SCALE}
        elif line.startswith("R "):
            out[cur]["r"] = _ints(line[2:])
        elif line.startswith("V "):
            out[cur]["v"] = _ints(line[2:])
    return out


def _ints(s: str) -> np.ndarray:
    """The fixed-point integers, as float32 values (value = n / 1e6)."""
    return np.array([int(t) for t in s.split()], dtype=np.int64)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=300)
    ap.add_argument("--steps", type=int, default=300)
    ap.add_argument("--points", type=int, default=8)
    ap.add_argument("--max-delay", type=int, default=10)
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--reps", type=int, default=1)
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--no-build", action="store_true")
    args = ap.parse_args()

    binary = build_binary(HERE / "montbrio_sweep", force=args.build or not args.no_build
                          and not (HERE / "montbrio_sweep").exists())
    scales = np.linspace(0.0, 5.0, args.points) if args.points > 1 else np.array([2.0])
    job = Job(args.n, args.steps, args.points, args.max_delay, scales)

    best = None
    for _ in range(args.reps):
        text, dt = run_bend(binary, job, HERE / "jobdir", threads=args.threads)
        best = dt if best is None else min(best, dt)
    res = parse_out(text)

    print(f"n={args.n} steps={args.steps} points={args.points} "
          f"max_delay={args.max_delay} threads={args.threads}")
    print(f"bend sweep wall-time: {best * 1e3:.1f} ms")
    for k in sorted(res):
        r, v = res[k].get("r"), res[k].get("v")
        print(f"  point {k} scale={res[k]['scale']:.3f} "
              f"r[0]={r[0] / 1e6:.6g} r[-1]={r[-1] / 1e6:.6g} "
              f"v[0]={v[0] / 1e6:.6g} v[-1]={v[-1] / 1e6:.6g} n={r.size}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
