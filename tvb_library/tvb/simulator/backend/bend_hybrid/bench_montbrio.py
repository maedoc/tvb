#!/usr/bin/env python
"""Benchmark: Bend sweep vs the numba hybrid, at bench_cpp_vs_numba.py scale.

The baseline is the one in `bench_cpp_vs_numba.py`: eight sweep points run
SEQUENTIALLY by numba, because that is how the numba sweep is driven there.
Bend runs the same eight points in one process, fanned out over the cores, so
the comparison is "eight points, whole pipeline" against "eight points, one at a
time" -- both including the array/buffer setup for every point.

Also reported, so the numbers can be read honestly:
  * the per-point cost of each backend, which is what the sweep multiplies;
  * Bend single-threaded, to separate "per-point speed" from "fan-out".

    python bench_montbrio.py --n 300 --steps 300 --points 8 --threads 8
"""
from __future__ import annotations

import argparse
import statistics
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from run_montbrio import Job, build_binary, run_bend  # noqa: E402
import compare_montbrio as C  # noqa: E402


def best_of(fn, warmup: int, reps: int) -> tuple[float, list[float]]:
    for _ in range(warmup):
        fn()
    ts = []
    for _ in range(reps):
        t0 = time.perf_counter()
        fn()
        ts.append(time.perf_counter() - t0)
    return min(ts), ts


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=300)
    ap.add_argument("--steps", type=int, default=300)
    ap.add_argument("--points", type=int, default=8)
    ap.add_argument("--max-delay", type=int, default=10)
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--warmup", type=int, default=2)
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()

    scales = (np.linspace(0.0, 5.0, args.points) if args.points > 1
              else np.array([2.0]))
    job = Job(args.n, args.steps, args.points, args.max_delay, scales,
              seed=args.seed)
    binary = build_binary(HERE / "montbrio_sweep", force=False)
    print(f"n={args.n} nodes, nstep={args.steps}, points={args.points}, "
          f"max_delay={args.max_delay}, threads={args.threads}, "
          f"warmup={args.warmup}, reps={args.reps}")
    print(f"connectome: {job.nnz} directed edges (dense, zero diagonal), "
          f"delays 0..{args.max_delay} steps, ring {job.hslots} slots")

    # ---- Bend: the whole sweep in one process -------------------------
    t_bend, ts_bend = best_of(
        lambda: run_bend(binary, job, HERE / "jobdir_bench",
                         threads=args.threads),
        args.warmup, args.reps)

    # ---- Bend: a single point, so the per-point cost is visible ---------
    job1 = Job(args.n, args.steps, 1, args.max_delay, np.array([2.0]),
               seed=args.seed)
    job1.delays = job.delays.copy()
    t_bend1, _ = best_of(
        lambda: run_bend(binary, job1, HERE / "jobdir_bench1", threads=1),
        1, args.reps)

    # ---- numba: the same points, one at a time (the bench baseline) -----
    solos = []
    for k in range(args.points):
        j = Job(args.n, args.steps, 1, args.max_delay, np.array([scales[k]]),
                seed=args.seed)
        j.delays = job.delays.copy()
        solos.append(j)

    def numba_sweep():
        for j in solos:
            C.ref_run(j, args.steps)

    t_nb, ts_nb = best_of(numba_sweep, 1, max(2, args.reps // 2))

    # ---- numba: a single point ------------------------------------------
    t_nb1, _ = best_of(lambda: C.ref_run(solos[0], args.steps), 1,
                       max(2, args.reps // 2))

    speed = t_nb / t_bend
    print()
    print(f"{'':22s} {'sweep (8 pts)':>16s} {'per point':>12s}")
    print(f"{'bend (this prototype)':22s} {t_bend * 1e3:13.1f} ms "
          f"{t_bend / args.points * 1e3:9.1f} ms")
    print(f"{'numba (sequential pts)':22s} {t_nb * 1e3:13.1f} ms "
          f"{t_nb / args.points * 1e3:9.1f} ms")
    print(f"{'bend, single point, 1 thr':22s} {'-':>16s} "
          f"{t_bend1 * 1e3:9.1f} ms")
    print(f"{'numba, single point':22s} {'-':>16s} "
          f"{t_nb1 * 1e3:9.1f} ms")
    print()
    print(f"per-point: bend is {t_bend1 / t_nb1:.2f}x numba "
          f"(single core, so this is the raw kernel gap)")
    print(f"sweep:     bend is {speed:.2f}x numba "
          f"({'PASS' if t_bend <= t_nb else 'FAIL'}: needs bend <= numba)")
    print(f"reps: bend min {min(ts_bend) * 1e3:.1f} ms median "
          f"{statistics.median(ts_bend) * 1e3:.1f} ms | numba min "
          f"{min(ts_nb) * 1e3:.1f} ms median {statistics.median(ts_nb) * 1e3:.1f} ms")
    return 0 if t_bend <= t_nb else 1


if __name__ == "__main__":
    raise SystemExit(main())
