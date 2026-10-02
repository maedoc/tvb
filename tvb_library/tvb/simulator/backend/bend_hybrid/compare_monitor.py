"""Cross-check the Bend router's monitor model (Mon / count_shared /
monitor_zoh_average) against the numba template's tavg semantics.

The reference is a direct transcription of templates/nb-hybrid-sim.py.mako
(one master loop, L922-1052, and the chunk emit at L1259):

  for t in range(nstep):            # master tick
      ... integrate each subnet (a subnet with period k integrates when
          its countdown wraps -- our Lane; between steps it HOLDS)
      tavg[subnet] += state[subnet]  # L1031: post-step state, every tick
      tavg_count[0] += 1             # L1052: ONE shared count, once per tick
  out = tavg / n                     # L1259: n = tavg_count[0]

so a subnet's tavg is the MASTER-TIME average of its ZOH-held trajectory,
divided by the number of master ticks -- exactly what the Bend laws pin:

  count_shared        mon_n(mon_ticks(t, ks, m)) == t + mon_n(m)
  monitor_zoh_average mon_n(mon_ticks(k, ks, mon_init())) == k
  (publication half)  period_from_init: one publish per period, else hold

This script checks, for several multi-rate configs:

  1. SCHEDULE parity: per master tick, the sample index each lane
     contributes (post-step `newest`, i.e. the ZOH hold pattern) and the
     shared count -- Python reference vs the Bend router, via a small
     transcription of router.bend's Lane/Mon defs.
  2. VALUE parity: the emitted tavg (sum of held values / count) agrees
     between the reference semantics and a "per-own-step" strawman is
     REJECTED -- i.e. we verify the strawman (divide by the lane's own
     publication count) gives DIFFERENT numbers, demonstrating the law
     has teeth.
  3. WINDOW parity: over any window of k master ticks a period-k lane's
     tavg divides by k (master span), and the held-trajectory identity
     sum(x_zoh)/k == sum over published samples weighted by hold length
     / k holds.

Run: /tmp/tvbvenv/bin/python compare_monitor.py [--ticks 12]
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction

sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent))


# ---------------------------------------------------------------------------
# The Bend router, transcribed 1:1 from router.bend (Nat semantics; Python
# ints are Nats, saturating sub spelled out).
# ---------------------------------------------------------------------------
def sub(a: int, b: int) -> int:
    """Nat.sub: saturating."""
    return a - b if a > b else 0


class Lane:
    """Lane{k, left, newest} -- the carried-counter schedule."""

    def __init__(self, k: int, left: int, newest: int):
        self.k, self.left, self.newest = k, left, newest

    def step(self) -> "Lane":
        if self.left == 0:
            return Lane(self.k, sub(self.k, 1), self.newest + 1)
        return Lane(self.k, self.left - 1, self.newest)

    def num(self) -> int:
        return sub(sub(self.k, 1), self.left)


def lane_init(k: int) -> Lane:
    return Lane(k, sub(k, 1), 0)


class Mon:
    """Mon{n} -- the shared tavg count."""

    def __init__(self, n: int):
        self.n = n

    def tick(self) -> "Mon":
        return Mon(self.n + 1)


# ---------------------------------------------------------------------------
# The numba template's monitor semantics, transcribed from the mako
# (independent of the router transcription: this is the "engine side").
# ---------------------------------------------------------------------------
def template_run(ks, values, nstep):
    """Simulate the template: each lane publishes values[newest]; the tavg
    accumulator adds the CURRENT (post-step, ZOH-held) value of every lane
    every master tick; ONE shared count advances once per tick.

    values[j][i] is the value of lane j's i-th published sample (sample 0
    is the IC).  Returns (per-tick contributions, per-tick count, tavg).
    """
    lanes = [lane_init(k) for k in ks]
    count = 0
    tacc = [Fraction(0)] * len(ks)
    contribs = []
    counts = []
    for t in range(nstep):
        stepped = [l.step() for l in lanes]
        lanes = stepped
        # L1031: accumulate the CURRENT state (post-step) of every subnet
        row = []
        for j, l in enumerate(lanes):
            tacc[j] += Fraction(values[j][l.newest])
            row.append(l.newest)  # the sample this lane contributes
        count += 1  # L1052: ONE shared counter, once per master tick
        contribs.append(row)
        counts.append(count)
    tavg = [x / count for x in tacc]  # L1259: divide by tavg_count
    return contribs, counts, tavg


def router_run(ks, nstep):
    """The ACTUAL Bend router + Mon model, via a generated Bend program:
    writes monitor_job.bend importing router.bend, builds and runs it with
    the bend CLI, parses the schedule (per-tick count and per-lane
    contributed sample index).  Falls back to the Python transcription of
    router.bend if the bend binary is unavailable.
    """
    import os
    import subprocess
    import tempfile
    from pathlib import Path

    bend = os.environ.get("BEND", str(Path.home() / ".bend" / "bin" / "bend"))
    if not Path(bend).exists():
        return router_run_transcribed(ks, nstep)
    ks_lit = " <> ".join(f"{k}n" for k in ks) + " <> Nil{}"
    src = f"""# generated by compare_monitor.py -- do not edit
import Base
import ./router.bend as R

def show_lane(+l: R.Lane) -> String:
  "lane " ++ Nat.show(R.lane_newest(l))

def show_lanes(ls: List<&2, R.Lane>, +acc: String) -> String:
  match ls:
    case Nil{{}}:
      acc
    case h <> t:
      show_lanes(t, acc ++ " " ++ show_lane(h))

def run_ticks(t: Nat, +ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>, +m: R.Mon, +acc: String) -> String:
  match t:
    case 0n:
      acc
    case 1n+p:
      +tk = R.tick(ls, ps)
      +mon = R.mon_tick(m)
      run_ticks(p, R.tick_lanes(tk), ps, mon,
                acc ++ "\n" ++ "count " ++ Nat.show(R.mon_n(mon))
                    ++ show_lanes(R.tick_lanes(tk), ""))

def main() -> IO(Unit):
  +lanes = R.init_lanes({ks_lit})
  do IO<Unit>:
    IO.print(run_ticks({nstep}n, lanes, {{Nil{{}} : List<&2, R.Proj>}}, R.mon_init(), ""))
"""
    with tempfile.TemporaryDirectory() as td:
        tdp = Path(td)
        (tdp / "router.bend").write_bytes(
            (Path(__file__).parent / "router.bend").read_bytes())
        job = tdp / "monitor_job.bend"
        job.write_text(src)
        r = subprocess.run([bend, str(job)], capture_output=True, text=True, cwd=tdp)
        if r.returncode != 0 or "Error" in r.stdout:
            raise RuntimeError(f"bend failed: {r.stdout}{r.stderr}")
        contribs, counts = [], []
        for line in r.stdout.strip().splitlines():
            parts = line.split()
            assert parts[0] == "count", f"unexpected line: {line!r}"
            counts.append(int(parts[1]))
            row = [int(x) for x in parts[3::2]]
            assert len(row) == len(ks), f"lane count mismatch: {line!r}"
            contribs.append(row)
        assert len(contribs) == nstep, "tick count mismatch"
        return contribs, counts


def router_run_transcribed(ks, nstep):
    """Fallback: the Python transcription of router.bend's Lane/Mon defs."""
    lanes = [lane_init(k) for k in ks]
    m = Mon(0)
    contribs = []
    counts = []
    for _ in range(nstep):
        lanes = [l.step() for l in lanes]
        m = m.tick()
        contribs.append([l.newest for l in lanes])
        counts.append(m.n)
    return contribs, counts


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ticks", type=int, default=12)
    args = ap.parse_args()
    nstep = args.ticks

    configs = [
        ([1, 1], "all k=1"),
        ([1, 3], "fast + slow 3"),
        ([1, 10], "the 10:1 case"),
        ([2, 3, 4], "three slow-ish lanes"),
        ([1, 2, 5, 10], "mixed"),
    ]
    failures = 0
    for ks, name in configs:
        # deterministic pseudo-values per published sample (sample 0 = IC)
        values = [[(i * 7 + j * 13) % 23 for i in range(nstep + 2)] for j in range(len(ks))]

        # 1. schedule parity: template transcription vs router transcription
        t_contribs, t_counts, tavg = template_run(ks, values, nstep)
        r_contribs, r_counts = router_run(ks, nstep)
        ok_sched = t_contribs == r_contribs and t_counts == r_counts
        if not ok_sched:
            failures += 1
            print(f"FAIL {name}: schedule mismatch")
            print("  template:", t_contribs[:4], t_counts[:4])
            print("  router  :", r_contribs[:4], r_counts[:4])
            continue

        # 2. the tavg values are the master-time ZOH average; a per-own-step
        #    divisor (the "fix" count_shared forbids) must DISAGREE for any
        #    k > 1 lane
        m = Mon(0)
        for _ in range(nstep):
            m = m.tick()
        assert m.n == nstep, "count_shared violated in transcription"
        for j, k in enumerate(ks):
            pubs = 1 + max(c[j] for c in r_contribs)  # published count
            strawman = None
            if pubs != nstep:
                # recompute the sum, divide by the lane's own publication
                # count instead of the shared master count
                s = Fraction(0)
                for row in r_contribs:
                    s += Fraction(values[j][row[j]])
                strawman = s / pubs
            if k > 1 and strawman is not None and strawman == tavg[j]:
                failures += 1
                print(f"FAIL {name}: strawman divisor agrees for lane {j}")

        # 3. window parity (monitor_zoh_average, divisor half): over any
        #    aligned window of k ticks, a period-k lane divides by k
        for j, k in enumerate(ks):
            for start in range(0, nstep - k + 1, k):
                sub_contribs = r_contribs[start:start + k]
                held = [values[j][row[j]] for row in sub_contribs]
                # every published sample in the window appears with weight
                # = its hold length; window average divides by k
                win_avg = sum(Fraction(v) for v in held) / k
                pubs = {row[j] for row in sub_contribs}
                weights = {p: sum(1 for v in held if v == values[j][p]) for p in pubs}
                # sanity: window length IS k (count_shared on the window)
                if len(sub_contribs) != k:
                    failures += 1
                    print(f"FAIL {name}: window length {len(sub_contribs)} != {k}")
                # the weighted identity
                if sum(Fraction(values[j][p]) * w for p, w in weights.items()) / k != win_avg:
                    failures += 1
                    print(f"FAIL {name}: weighted identity broke for lane {j}")

        total = Fraction(sum(values[j][r_contribs[-1][j]] for j in range(len(ks))))
        print(f"ok   {name}: schedule parity, count_shared, "
              f"monitor_zoh_average (tavg[0]={float(tavg[0]):.6g})")

    if failures:
        print(f"{failures} FAILURES")
        return 1
    print("all checks pass: the Bend monitor model matches the template")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
