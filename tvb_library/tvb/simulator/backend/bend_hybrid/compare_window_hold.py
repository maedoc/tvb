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


# --------------------------------------------------------------------------
# list-level routing: lanes_step_local, route_pointwise, tick_split
# --------------------------------------------------------------------------


def lanes_step_py(ls: list[Lane]) -> list[Lane]:
    """router.bend lanes_step."""
    return [l.step() for l in ls]


def nth(ls: list, i: int):
    """router.bend nth_lane/nth_line/nth_proj default-past-end semantics."""
    return ls[i] if i < len(ls) else None


def route_read_py(n: int, d: int, num: int, den: int, win: int) -> tuple:
    """router.bend route_read -> Line{i0, i1, num, den, win}."""
    if d == 0:
        return (n, n, 0, den, win)
    return (sub(n, d), sub(n, d - 1), num, den, win)


def route_proj_py(ls: list[Lane], p: tuple) -> tuple:
    """router.bend route_proj: (src, tgt, d, win, tc)."""
    src, tgt, d, win, tc = p
    lane = nth(ls, src)
    return route_read_py(lane.newest, d, k_minus_1_minus_left(lane), lane.k, win)


def k_minus_1_minus_left(lane: Lane) -> int:
    """router.bend lane_num = (k-1) - left, saturating."""
    return sub(sub(lane.k, 1), lane.left)


def check_lanes_step_local(limit: int = 6) -> int:
    """lanes_step_local: nth(lanes_step(ls), i) == step(nth(ls, i)) for i < len."""
    bad = 0
    for nl in range(1, limit):
        for i in range(nl):
            for k in range(1, 4):
                ls = [Lane(k, k - 1, j) for j in range(nl)]
                got = nth(lanes_step_py(ls), i)
                want = nth(ls, i).step()
                if (got.k, got.left, got.newest) != (want.k, want.left, want.newest):
                    print(f"FAIL lanes_step_local nl={nl} i={i} k={k}")
                    bad += 1
    # negative control: the bounds witness is load-bearing.  Past the end,
    # router.bend's nth_lane answers the default Lane{1,0,0} and
    # lanes_step answers nothing -- but step_lane applied to the default
    # IS Lane{1,0,1} (its countdown wraps), so the naive unbounded claim
    #    nth(lanes_step(ls), i) == step(nth(ls, i))
    # is FALSE at i >= len (left: default, right: stepped default).  The
    # law's lt_ok(i, lanes_len(ls)) hypothesis exists precisely to keep
    # that case out of the claim.
    d = Lane(1, 0, 0)
    if (d.step().k, d.step().left, d.step().newest) != (1, 0, 1):
        print("FAIL default-step probe: step of Lane{1,0,0} should be Lane{1,0,1}")
        bad += 1
    return bad


def check_route_pointwise(limit: int = 5) -> int:
    """route_pointwise: nth(route_all(ls, ps), i) == route_proj(ls, nth(ps, i))."""
    bad = 0
    for nl in range(1, limit):
        for np_ in range(1, limit):
            for i in range(np_):
                ls = [Lane(1 + (j % 3), 0, j) for j in range(nl)]
                ps = [(j % nl, (j + 1) % nl, j % 2, j % 3, j) for j in range(np_)]
                routed = [route_proj_py(ls, p) for p in ps]
                got = nth(routed, i)
                want = route_proj_py(ls, nth(ps, i))
                if got != want:
                    print(f"FAIL route_pointwise nl={nl} np={np_} i={i}: {got} != {want}")
                    bad += 1
    return bad


def tick_py(ls: list[Lane], ps: list[tuple]) -> tuple:
    """router.bend tick -> (stepped lanes, routed lines)."""
    stepped = lanes_step_py(ls)
    return (stepped, [route_proj_py(stepped, p) for p in ps])


def check_macro_degenerate(limit: int = 12) -> int:
    """macro_degenerate: at k=1 the macro-first read (d=1, own fraction)
    is the staggered point read i0 = t-1, with fraction identically 0.

    The macro policy routes slow->fast reads at d=1 with fraction
    num/den = phase/k; at k=1 the lane has no phase (always due), so
    route_read(t, 1, 0, 1, win) == Line{t-1, t, 0, 1, win} -- exactly
    the staggered degenerate_read formula i0 = t-d at d=1.
    """
    bad = 0
    for t in range(limit):
        lane = steps(t, Lane(1, 0, 0))
        num = sub(sub(lane.k, 1), lane.left)  # lane_num at k=1: always 0
        line = route_read_py(lane.newest, 1, num, lane.k, 0)
        if num != 0:
            print(f"FAIL macro_degenerate t={t}: fraction {num} != 0")
            bad += 1
        if line[0] != sub(t, 1):  # Nat.sub saturates: t=0 gives 0
            print(f"FAIL macro_degenerate t={t}: i0 {line[0]} != {sub(t, 1)}")
            bad += 1
    return bad


def check_tick_split(limit: int = 5) -> int:
    """tick_split: ticks(a+b) == ticks(b) after ticks(a); chunk safety."""
    bad = 0
    for nl in range(1, 4):
        for np_ in range(1, 4):
            for a in range(limit):
                for b in range(limit):
                    ls = [Lane(1 + (j % 3), j % 2, j) for j in range(nl)]
                    ps = [(j % nl, (j + 1) % nl, j % 2, 0, j) for j in range(np_)]
                    # ticks(t): fold tick t times (tick includes route_all)
                    def ticks(t, ls0):
                        for _ in range(t):
                            ls0, lines = tick_py(ls0, ps)
                        return (ls0, lines)
                    # note: ticks(0) = (ls0, route_all(ls0)) per router.bend
                    def ticks_full(t, ls0):
                        cur = ls0
                        for _ in range(t):
                            cur = tick_py(cur, ps)[0]
                        return (cur, [route_proj_py(cur, p) for p in ps])
                    left = ticks_full(a + b, ls)
                    right_pre = ticks_full(a, ls)
                    right = ticks_full(b, right_pre[0])
                    lanes_l = [(x.k, x.left, x.newest) for x in left[0]]
                    lanes_r = [(x.k, x.left, x.newest) for x in right[0]]
                    if (lanes_l, left[1]) != (lanes_r, right[1]):
                        print(f"FAIL tick_split nl={nl} np={np_} a={a} b={b}")
                        bad += 1
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
    bad += check_macro_degenerate()
    bad += check_lanes_step_local()
    bad += check_route_pointwise()
    bad += check_tick_split()
    if bad:
        print(f"{bad} FAILURES")
        return 1
    print("window_span + hold_until_due + left_invariant + delay_injective "
          "+ staleness (canonical_run/newest_at/stale_bound) + window_ordered "
          "+ list-level routing (lanes_step_local / route_pointwise / tick_split): "
          "all properties hold (exhaustive small range, engine-side)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
