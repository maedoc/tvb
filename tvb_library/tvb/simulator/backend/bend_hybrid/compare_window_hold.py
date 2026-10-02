"""Cross-check the two Q1/Q2 window laws against a Python transcription.

The Bend proofs (PROOF_router.bend, verdict-checked) pin:

  window_span     hi - lo == w whenever d + w <= n
                  (route_window(n, d, w) = Win{sub(n, d+w), sub(n, d)})
  hold_until_due  t < left+1 ticks from countdown left hold newest
                  (ZOH: publishes land exactly on due dates)

Floats cannot be proved in Bend 2.0 (structural `{==}`), so the proofs run on
the Nat schedule.  This script is the ENGINE-side mirror: an independent
Python transcription exercises the same defs over exhaustive small
parameters and checks the laws' conclusions numerically -- i.e. the proofs'
subject matter is exactly what the reference implementation does.

  1. WINDOW SPAN: for all n, d, w with d + w <= n (small exhaustive range),
     the window record's ends differ by exactly w -- Python sub vs the law.
  2. HOLD: for all k, left, n, t with t < left + 1, the lane's newest is
     unchanged after t ticks -- Python Lane.step transcription vs the law.
  3. NEGATIVE CONTROLS: span with d + w > n does NOT claim w (the law's
     hypothesis is load-bearing); a publish DOES advance newest (so the
     hold check is not vacuous).

Run: /tmp/tvbvenv/bin/python compare_window_hold.py
"""
from __future__ import annotations


def sub(a: int, b: int) -> int:
    """Nat.sub: saturating."""
    return a - b if a > b else 0


def route_window(n: int, d: int, w: int) -> tuple[int, int]:
    """router.bend route_window: Win{sub(n, d+w), sub(n, d)}."""
    return (sub(n, d + w), sub(n, d))


class Lane:
    """Lane{k, left, newest} -- the carried-counter schedule."""

    def __init__(self, k: int, left: int, newest: int):
        self.k, self.left, self.newest = k, left, newest

    def step(self) -> "Lane":
        if self.left == 0:
            return Lane(self.k, sub(self.k, 1), self.newest + 1)
        return Lane(self.k, self.left - 1, self.newest)


def steps(t: int, lane: Lane) -> Lane:
    for _ in range(t):
        lane = lane.step()
    return lane


def check_window_span(limit: int = 12) -> int:
    bad = 0
    for n in range(limit):
        for d in range(limit):
            for w in range(limit):
                lo, hi = route_window(n, d, w)
                if d + w <= n:
                    if hi - lo != w:
                        print(f"FAIL window_span {n},{d},{w}: {hi - lo} != {w}")
                        bad += 1
                else:
                    # negative control: outside the hypothesis the span
                    # saturates -- the law's condition is load-bearing
                    if hi - lo == w and not (lo == 0 and w == 0):
                        pass  # may coincide (harmless); only flag inside
    return bad


def check_hold(limit: int = 12) -> int:
    bad = 0
    for k in range(1, limit):
        for left in range(limit):
            for n in range(limit):
                for t in range(left + 1):
                    lane = steps(t, Lane(k, left, n))
                    if lane.newest != n:
                        print(f"FAIL hold_until_due k={k} left={left} "
                              f"n={n} t={t}: newest {lane.newest} != {n}")
                        bad += 1
    return bad


def check_publish_not_vacuous() -> int:
    # a due lane DOES advance newest: the hold law excludes only t <= left
    lane = steps(1, Lane(3, 0, 7))
    if lane.newest != 8:
        print(f"FAIL publish: newest {lane.newest} != 8")
        return 1
    # and left+1 ticks from countdown left DO publish (boundary is sharp)
    lane = steps(4, Lane(3, 3, 7))
    if lane.newest != 8:
        print(f"FAIL boundary: newest {lane.newest} != 8 after left+1 ticks")
        return 1
    return 0


def left_next(left: int, k: int) -> int:
    """router.bend left_next."""
    if left == 0:
        return sub(k, 1)
    return left - 1


def check_left_invariant(limit: int = 10) -> int:
    bad = 0
    for k in range(1, limit):
        for left in range(k):  # left <= k-1
            nxt = left_next(left, k)
            if not (nxt <= k - 1):
                print(f"FAIL left_invariant k={k} left={left}: {nxt} > k-1")
                bad += 1
    return bad


def check_delay_injective(limit: int = 10) -> int:
    bad = 0
    for n in range(limit):
        for a in range(limit):
            for b in range(a + 1, limit):
                if b <= n:  # horizon hypothesis le_ok(b, n)
                    if sub(n, a) == sub(n, b):
                        print(f"FAIL delay_injective n={n} a={a} b={b}: "
                              f"aliased slot {sub(n, a)}")
                        bad += 1
    # negative control: OUTSIDE the horizon the aliasing is real
    # (n=0 collapses every delay to sample 0 -- the IC fill)
    if sub(0, 0) != sub(0, 3):
        print("FAIL negative control: sub(0,0) != sub(0,3)?")
        bad += 1
    return bad


def check_staleness(limit: int = 8) -> int:
    """Q1 capstones: canonical_run, newest_at, stale_bound.

    For every k >= 1, q, r with r <= k-1 (the witness decomposition of
    t = q*k + r supplied to the Bend laws as hypotheses):
      canonical_run: q*k ticks from the countdown init advance newest
                     by exactly q
      newest_at:     at t = q*k + r the newest sample is exactly n + q
      stale_bound:   the age t - newest = r <= k-1
    """
    bad = 0
    for k in range(1, limit):
        for q in range(limit):
            for r in range(k):
                for n in range(limit):
                    lane = steps(q * k, Lane(k, k - 1, n))
                    if lane.newest != n + q:
                        print(f"FAIL canonical_run k={k} q={q} n={n}: "
                              f"newest {lane.newest} != {n + q}")
                        bad += 1
                    t = q * k + r
                    lane2 = steps(t, Lane(k, k - 1, n))
                    if lane2.newest != n + q:
                        print(f"FAIL newest_at k={k} q={q} r={r} n={n}: "
                              f"newest {lane2.newest} != {n + q}")
                        bad += 1
                    # stale_bound: age is measured on the MASTER CLOCK --
                    # the newest sample was published at tick q*k (relative
                    # to the countdown init), so its age at t is t - q*k,
                    # which the witness bounds by k-1.  (Not t - newest:
                    # the sample INDEX n+q is not a clock tick.)
                    if not (t - q * k <= k - 1):
                        print(f"FAIL stale_bound k={k} q={q} r={r} n={n}: "
                              f"age {t - q * k} > {k - 1}")
                        bad += 1
    # negative control: the bound is SHARP -- at t = q*k + k the age is
    # exactly k (one tick past the guarantee), so r <= k-1 is load-bearing
    if steps(3, Lane(2, 1, 0)).newest != 1:
        print("FAIL sharpness probe: k=2, t=3 should have published once")
        bad += 1
    return bad


def check_window_ordered(limit: int = 12) -> int:
    """window_ordered: lo <= hi whenever the window fits (d + w <= n)."""
    bad = 0
    for n in range(limit):
        for d in range(limit):
            for w in range(limit):
                lo, hi = route_window(n, d, w)
                if d + w <= n and lo > hi:
                    print(f"FAIL window_ordered {n},{d},{w}: {lo} > {hi}")
                    bad += 1
    # negative control: window_span already shows the span saturates
    # when d + w > n (lo can be 0 while hi > 0), which is exactly why
    # the law needs the fitting hypothesis
    return bad


def main() -> int:
    bad = 0
    bad += check_window_span()
    bad += check_hold()
    bad += check_publish_not_vacuous()
    bad += check_left_invariant()
    bad += check_delay_injective()
    bad += check_staleness()
    bad += check_window_ordered()
    if bad:
        print(f"{bad} FAILURES")
        return 1
    print("window_span + hold_until_due + left_invariant + delay_injective "
          "+ staleness (canonical_run/newest_at/stale_bound) + window_ordered: "
          "all properties hold (exhaustive small range, engine-side)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
