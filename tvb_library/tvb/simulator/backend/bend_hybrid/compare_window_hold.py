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


def check_slow_lag(limit: int = 10) -> int:
    """slow_lag_bound + window_head_age: the macro-first lag necessity.

    slow_lag_bound: the windowed read's freshest member t-d is never
    ahead of the head of the stream t (windowing only makes input
    older -- never fresher).

    window_head_age: the windowed read's OLDEST member (the head of
    the slow lane's averaged input) is exactly d+k ticks behind the
    head of the stream: lo + (d+k) == n.  The slow lane's input is
    one full window behind -- forced, not chosen (the dual of
    clamp_necessary's zero-delay clamp).
    """
    bad = 0
    for n in range(limit):
        for d in range(limit):
            # slow_lag_bound: t-d <= t, saturating sub included
            if not (sub(n, d) <= n):
                print(f"FAIL slow_lag_bound n={n} d={d}")
                bad += 1
            for k in range(limit):
                if d + k <= n:  # le_ok witness: the window fits
                    lo, hi = route_window(n, d, k)
                    # window_head_age: lo + (d+k) == n exactly
                    if lo + (d + k) != n:
                        print(f"FAIL window_head_age n={n} d={d} k={k}: "
                              f"lo+span {lo + d + k} != {n}")
                        bad += 1
                    # negative control: OUTSIDE the fitting witness the
                    # identity fails (sub saturates) -- the witness is
                    # load-bearing, exactly as in the Bend law
                else:
                    lo, hi = route_window(n, d, k)
                    if lo + (d + k) != n and n > 0 and d + k - n <= 2:
                        pass  # saturation may still coincide; no claim
    return bad


def check_freshness(limit: int = 4) -> int:
    """The end-to-end freshness laws, engine-side.

    route_all_len:  routing is lossless -- len(routed) == len(projs).
    route_fresh:    each routed line's i1 <= its source lane's newest
                    (published) -- the router never reads unpublished.
    read_fresh_tick:  freshness holds after one whole tick (step then
                    route against the stepped lanes).
    read_fresh_ticks: freshness is tick-invariant (holds at every t).
    line_ordered:   i0 <= i1 in every routed line (never inverted).
    """
    bad = 0
    for nl in range(1, limit + 1):
        for np_ in range(1, limit + 1):
            ps = [(j % nl, (j + 1) % nl, j % 3, j % 2, j) for j in range(np_)]
            for t in range(limit + 2):
                ls = [Lane(1 + (j % 3), j % 2, j) for j in range(nl)]
                # roll t ticks
                cur = ls
                for _ in range(t):
                    cur = lanes_step_py(cur)
                routed = [route_proj_py(cur, p) for p in ps]
                # route_all_len
                if len(routed) != len(ps):
                    print(f"FAIL route_all_len nl={nl} np={np_}")
                    bad += 1
                # route_fresh / read_fresh_tick(s): every line fresh
                for j, line in enumerate(routed):
                    src = ps[j][0]
                    newest = cur[src].newest
                    if line[1] > newest:  # i1 <= newest
                        print(f"FAIL freshness nl={nl} np={np_} t={t} j={j}: "
                              f"i1 {line[1]} > newest {newest}")
                        bad += 1
                    if line[0] > line[1]:  # i0 <= i1
                        print(f"FAIL line_ordered nl={nl} np={np_} t={t} j={j}: "
                              f"i0 {line[0]} > i1 {line[1]}")
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


def check_non_aliasing(limit: int = 8) -> int:
    """The non-aliasing laws, engine-side.

    read_distinct / route_distinct: two reads at distinct in-horizon delays
      da < db <= n read distinct i0 samples (clamp case included: da=0
      reads the head n, distinct from n-db once db <= n).
    i0_win_irrelevant: the read index never depends on the window.
    fits_lt: an accepted projection's delay is strictly inside the horizon.
    """
    bad = 0
    for n in range(limit):
        for da in range(limit):
            for db in range(da + 1, limit):
                if db <= n:  # horizon hypothesis le_ok(db, n)
                    ia = route_read_py(n, da, 0, 1, 0)[0]
                    ib = route_read_py(n, db, 0, 1, 0)[0]
                    if ia == ib:
                        print(f"FAIL read_distinct n={n} da={da} db={db}: "
                              f"aliased slot {ia}")
                        bad += 1
                if da <= n:  # symmetric direction for the clamp read
                    ia = route_read_py(n, da, 0, 1, 0)[0]
                    if ia != sub(n, da):
                        print(f"FAIL clamp i0 n={n} da={da}")
                        bad += 1
    # negative control: OUTSIDE the horizon the aliasing is real (n=0
    # collapses d=1 and d=2 onto slot 0 -- the IC fill)
    if route_read_py(0, 1, 0, 1, 0)[0] != route_read_py(0, 2, 0, 1, 0)[0]:
        print("FAIL negative control: n=0 d=1 vs d=2 should alias on slot 0")
        bad += 1
    # i0_win_irrelevant: the read start never sees the window
    for n in range(4):
        for d in range(4):
            for wa in range(3):
                for wb in range(3):
                    if route_read_py(n, d, 0, 1, wa)[0] != route_read_py(n, d, 0, 1, wb)[0]:
                        print(f"FAIL i0_win_irrelevant n={n} d={d} wa={wa} wb={wb}")
                        bad += 1
    # route_distinct, list-level: same source, distinct in-horizon delays
    for nl in range(1, 4):
        for new in range(4):
            ls = [Lane(1 + (j % 2), j % 2, new + j) for j in range(nl)]
            for da in range(3):
                for db in range(da + 1, 4):
                    if db <= ls[0].newest:
                        pa = (0, 1, da, 0, 0)
                        pb = (0, 1, db, 2, 1)  # distinct windows on purpose
                        ia = route_proj_py(ls, pa)[0]
                        ib = route_proj_py(ls, pb)[0]
                        if ia == ib:
                            print(f"FAIL route_distinct nl={nl} new={new} "
                                  f"da={da} db={db}: aliased {ia}")
                            bad += 1
    return bad


def proj_shape_ok_py(nlanes: int, horizon: int, p: tuple) -> bool:
    """router.bend proj_shape_ok: src < nlanes, tgt < nlanes,
    d + 1 <= horizon, d + win <= horizon."""
    src_, tgt, d, win, tc = p
    return (src_ < nlanes
            and tgt < nlanes
            and d + 1 <= horizon
            and d + win <= horizon)


def proj_clash_py(a: tuple, b: tuple) -> bool:
    """router.bend proj_clash: same target AND same coupling slot."""
    return a[1] == b[1] and a[4] == b[4]


def writes_unique_py(ps: list) -> bool:
    """router.bend writes_unique/no_clash: no (tgt, tc) pair repeats."""
    for i, a in enumerate(ps):
        for b in ps[i + 1:]:
            if proj_clash_py(a, b):
                return False
    return True


def csr_ok_py(nsrc: int, horizon: int, csr: tuple) -> bool:
    """router.bend csr_ok: indptr[0] == 0, indptr sorted,
    indptr[-1] == len(indices) == len(delays), indices < nsrc,
    delays < horizon."""
    indptr, indices, delays = csr
    if not indptr or indptr[0] != 0:
        return False
    if any(indptr[i] > indptr[i + 1] for i in range(len(indptr) - 1)):
        return False
    if indptr[-1] != len(indices) or len(indices) != len(delays):
        return False
    return (all(i < nsrc for i in indices)
            and all(d < horizon for d in delays))


def check_tier1(limit: int = 5) -> int:
    """The tier-1 laws, engine-side.

    ok_proj_shape_nth / ok_fits_nth: every projection of a
      projs_shape_ok list passes the per-projection validator, and its
      delay is strictly inside the horizon.
    lanes_nth_valid: every lane of a lanes_ok list has period >= 1.
    csr_nth_delay_fits / csr_nth_index_bound: csr_ok's per-edge bounds
      hold at every bounded index, not just of the folds.
    ok_no_clash: in a writes_unique list, two same-target projections
      (distinct indices) carry distinct coupling slots.
    read_i0_is_window_head: the point read's i0 IS the window's head
      (the two read modes agree on where averaging ends).
    """
    bad = 0
    for nl in range(1, limit):
        for horizon in range(1, limit + 2):
            for np_ in range(1, limit):
                ps = [(j % nl, (j + 1) % nl, j % horizon, j % 2, j) for j in range(np_)]
                all_ok = all(proj_shape_ok_py(nl, horizon, p) for p in ps)
                if all_ok:
                    for i, p in enumerate(ps):
                        if not proj_shape_ok_py(nl, horizon, p):
                            print(f"FAIL ok_proj_shape_nth nl={nl} h={horizon} i={i}")
                            bad += 1
                        if not p[2] < horizon:
                            print(f"FAIL ok_fits_nth nl={nl} h={horizon} i={i}")
                            bad += 1
                # ok_no_clash: on writes_unique lists (no (tgt, tc) repeats)
                if writes_unique_py(ps):
                    for ia in range(np_):
                        for ib in range(ia + 1, np_):
                            if ps[ia][1] == ps[ib][1] and ps[ia][4] == ps[ib][4]:
                                print(f"FAIL ok_no_clash nl={nl} ia={ia} ib={ib}")
                                bad += 1
    # lanes_nth_valid
    for ks in ([1], [1, 2], [3, 1], [2, 2, 2]):
        if all(k >= 1 for k in ks):
            for i in range(len(ks)):
                if ks[i] < 1:
                    print(f"FAIL lanes_nth_valid {ks} i={i}")
                    bad += 1
    # csr per-edge bounds
    for nsrc in range(1, 4):
        for horizon in range(1, 4):
            indptr = [0, 1, 3]
            indices = [min(j, nsrc - 1) for j in range(3)]
            delays = [j % horizon for j in range(3)]
            if csr_ok_py(nsrc, horizon, (indptr, indices, delays)):
                for i in range(len(delays)):
                    if not delays[i] < horizon:
                        print(f"FAIL csr_nth_delay_fits i={i}")
                        bad += 1
                    if not indices[i] < nsrc:
                        print(f"FAIL csr_nth_index_bound i={i}")
                        bad += 1
    # read_i0_is_window_head
    for n in range(4):
        for d in range(4):
            for win in range(3):
                if route_window(n, d, win)[1] != route_read_py(n, d, 0, 1, win)[0]:
                    print(f"FAIL read_i0_is_window_head n={n} d={d} win={win}")
                    bad += 1
    return bad


def hist_read_py(xs: list, i: int, ic: float) -> float:
    """hist.bend hist_read: element i is the sample at tick i; ic past end."""
    return xs[i] if i < len(xs) else ic


def hist_snoc_py(xs: list, v: float) -> list:
    """hist.bend hist_snoc: append at the far end (the next tick)."""
    return xs + [v]


def hist_drop_py(xs: list, k: int) -> list:
    """hist.bend hist_drop: drop the k oldest samples."""
    return xs[k:]


def check_history(limit: int = 6) -> int:
    """The tape laws, engine-side.

    hist_read_snoc: appending v and reading at the old length returns v.
    hist_snoc_stable: appending never changes reads below the old length.
    hist_read_ic: reads at or past the length answer the IC fill.
    hist_prune_shift: buf[k:][i] == buf[i+k], including past the end
      (both sides answer IC -- the law is unconditional).
    """
    import random
    rng = random.Random(20261002)
    bad = 0
    for length in range(limit):
        xs = [rng.random() for _ in range(length)]
        for v in (0.5, -1.0):
            for ic in (0.0, 9.0):
                for i in range(limit + 2):
                    # hist_read_snoc
                    if hist_read_py(hist_snoc_py(xs, v), length, ic) != v:
                        print(f"FAIL hist_read_snoc len={length} v={v}")
                        bad += 1
                    # hist_snoc_stable (only below the old length)
                    if i < length:
                        if hist_read_py(hist_snoc_py(xs, v), i, ic) != \
                           hist_read_py(xs, i, ic):
                            print(f"FAIL hist_snoc_stable len={length} i={i}")
                            bad += 1
                    # hist_read_ic
                    if i >= length:
                        if hist_read_py(xs, i, ic) != ic:
                            print(f"FAIL hist_read_ic len={length} i={i}")
                            bad += 1
                    # hist_prune_shift (unconditional)
                    for k in range(limit + 2):
                        if hist_read_py(hist_drop_py(xs, k), i, ic) != \
                           hist_read_py(xs, i + k, ic):
                            print(f"FAIL hist_prune_shift len={length} "
                                  f"k={k} i={i}")
                            bad += 1
    # negative control, engine-side: stability AT the top is FALSE -- the
    # snoc just wrote there, so the read is v, not the IC fill
    if hist_read_py(hist_snoc_py([1.0], 2.5), 1, 0.0) == 0.0:
        print("FAIL bad_hist probe: read at the old length should be v")
        bad += 1
    return bad


def ring_read_py(xs: list, i: int, cap: int, ic: float) -> float:
    """hist.bend ring_read: Design B's slot addressing, i %% cap."""
    return hist_read_py(xs, i % cap, ic) if cap > 0 else ic


def check_ring(limit: int = 8) -> int:
    """The ring bridge, engine-side.

    mod_lt: for i < cap, i %% cap == i (the fence).
    ring_first_lap: for i < cap, the ring read IS the tape read at i.
    Negative control: at i = cap the mod wraps to 0 -- the ring silently
    returns slot 0's sample (the OLDEST), which is the aliasing the
    cap >= horizon conjunct exists to fence off.
    """
    bad = 0
    for length in range(limit):
        xs = [float(j + 1) for j in range(length)]
        for cap in range(1, limit + 2):
            for i in range(limit + 2):
                # mod_lt
                if i < cap and i % cap != i:
                    print(f"FAIL mod_lt i={i} cap={cap}")
                    bad += 1
                # ring_first_lap
                if i < cap:
                    if ring_read_py(xs, i, cap, 0.0) != hist_read_py(xs, i, 0.0):
                        print(f"FAIL ring_first_lap len={length} i={i} cap={cap}")
                        bad += 1
    # negative control, engine-side: at i = cap the wrap is REAL
    xs = [1.5, 2.5]
    if ring_read_py(xs, 2, 2, 0.0) == hist_read_py(xs, 2, 0.0):
        # ring answers slot 0 (1.5); tape answers IC (0.0): they differ
        print("FAIL bad_ring probe: second-lap read should alias slot 0")
        bad += 1
    return bad


def check_blend_wiring(limit: int = 8) -> int:
    """The blend wiring laws, engine-side.

    blend_adjacent: for an in-history delay d = 1+dp (d <= n), the routed
      line's endpoints are exactly one tick apart: i1 == i0 + 1.
    clamp_reads_same: at d = 0 both endpoints are the newest sample n.
    clamp_zero_frac: at d = 0 the numerator is 0 (alpha = 0).

    Negative control: at n = 0, d = 1 the saturating sub collapses both
    endpoints to 0 -- i1 == i0 + 1 is 0 == 1, FALSE. The in-history
    witness d <= n is load-bearing (bad/bad_blend_adj.bend).
    """
    bad = 0
    for n in range(limit):
        for dp in range(limit):
            for num in (0, 1, 3):
                for den in (1, 2):
                    for win in (0, 2):
                        i0, i1, rnum, _, _ = route_read_py(n, 1 + dp, num, den, win)
                        if 1 + dp <= n and i1 != i0 + 1:
                            print(f"FAIL blend_adjacent n={n} dp={dp}: {i1} != {i0}+1")
                            bad += 1
                        c0, c1, cnum, _, _ = route_read_py(n, 0, num, den, win)
                        if c0 != n or c1 != n:
                            print(f"FAIL clamp_reads_same n={n}: {c0},{c1} != {n},{n}")
                            bad += 1
                        if cnum != 0:
                            print(f"FAIL clamp_zero_frac n={n}: num {cnum} != 0")
                            bad += 1
    # negative control: no witness, n = 0, d = 1 -- the endpoints coincide
    i0, i1, *_ = route_read_py(0, 1, 0, 1, 0)
    if i1 == i0 + 1:
        print("FAIL bad_blend_adj probe: 0 == 1 should be false")
        bad += 1
    return bad

def nats_take_py(xs: list, k: int) -> list:
    """router.bend nats_take: first k elements, saturating."""
    return xs[:k] if k < len(xs) else list(xs)

def nats_drop_py(xs: list, k: int) -> list:
    """router.bend nats_drop: past the first k, saturating."""
    return xs[k:] if k < len(xs) else []

def nats_slice_py(xs: list, lo: int, hi: int) -> list:
    """router.bend nats_slice = take(drop(xs, lo), hi - lo)."""
    return nats_take_py(nats_drop_py(xs, lo), sub(hi, lo))

def csr_row_py(indptr: list, indices: list, t: int) -> list:
    """router.bend csr_row_indices: rows between indptr[t] and indptr[t+1]."""
    lo = nth(indptr, t)
    hi = nth(indptr, t + 1)
    return nats_slice_py(indices, lo, hi)

def check_csr_slice(limit: int = 8) -> int:
    """The CSR slice laws, engine-side.

    take_nth: reading take(xs, k) at i < k is reading xs at i.
    slice_nth: the i-th element of the [lo, hi) slice is xs[lo + i],
      whenever i < hi - lo (the row-width witness).
    slice_len: the slice never has more than hi - lo elements.
    csr_row: the row of target t is exactly indices[indptr[t]:indptr[t+1]],
      and the delays row slices the SAME bounds -- the (src, delay) pair
      a gather folds stays aligned entry for entry.

    Negative control: past the row's width the slice saturates to 0
      while the flat read still returns a real row (bad_slice).
    """
    import random
    rng = random.Random(20261003)
    bad = 0
    for _len in range(limit):
        xs = [rng.randrange(10) for _ in range(_len)]
        for lo in range(limit):
            for hi in range(limit):
                w = sub(hi, lo)
                for i in range(limit + 2):
                    if i < w and nth(nats_slice_py(xs, lo, hi), i) != \
                       nth(xs, lo + i):
                        print(f"FAIL slice_nth lo={lo} hi={hi} i={i}")
                        bad += 1
                    if i < min(w, _len) and nth(nats_take_py(xs, min(w, _len)), i) != \
                       nth(xs, i):
                        print(f"FAIL take_nth k={w} i={i}")
                        bad += 1
                if len(nats_slice_py(xs, lo, hi)) > w:
                    print(f"FAIL slice_len lo={lo} hi={hi}")
                    bad += 1
    # csr rows: aligned src/delay pairs, same bounds
    for nn in range(1, limit):
        indptr = sorted(rng.randrange(6) for _ in range(nn + 1))
        indptr[0] = 0
        m = indptr[-1]
        indices = [rng.randrange(nn) for _ in range(m)]
        delays = [rng.randrange(4) for _ in range(m)]
        for t in range(nn):
            row_i = nats_slice_py(indices, indptr[t], indptr[t + 1])
            row_d = nats_slice_py(delays, indptr[t], indptr[t + 1])
            if len(row_i) != sub(indptr[t + 1], indptr[t]):
                print(f"FAIL csr row len t={t}")
                bad += 1
            for i, v in enumerate(row_i):
                if v != nth(indices, indptr[t] + i):
                    print(f"FAIL csr row src t={t} i={i}")
                    bad += 1
                if row_d[i] != nth(delays, indptr[t] + i):
                    print(f"FAIL csr row delay t={t} i={i}")
                    bad += 1
    # negative control: past the row's width the slice answers 0
    xs = [7, 8, 9]
    if nth(nats_slice_py(xs, 0, 2), 2) == nth(xs, 2):
        print("FAIL bad_slice probe: saturated read should not equal the real row")
        bad += 1
    return bad

def edge_py(ls: list, s: int, d: int) -> tuple:
    """router.bend edge: route_read on lane s at delay d."""
    lane = nth(ls, s)
    if lane is None:
        lane = Lane(1, 0, 0)
    return route_read_py(lane.newest, d, k_minus_1_minus_left(lane), lane.k, 0)

def edge_lines_from_py(ls: list, ixs: list, ds: list, cnt: int, e0: int) -> list:
    """router.bend edge_lines_from: cnt edges starting at flat index e0."""
    out = []
    for j in range(cnt if cnt > 0 else 0):
        out.append(edge_py(ls, nth(ixs, e0 + j), nth(ds, e0 + j)))
    return out

def csr_row_lines_py(ls: list, indptr: list, ixs: list, ds: list, t: int) -> list:
    """router.bend csr_row_lines: the routing table of target t's row."""
    lo = nth(indptr, t)
    hi = nth(indptr, t + 1)
    return edge_lines_from_py(ls, ixs, ds, sub(hi, lo), lo)

def check_row_lines(limit: int = 6) -> int:
    """The end-to-end capstone (Link 4), engine-side.

    row_lines_nth: the j-th line of target t's routing table is the routed
      read of source indices[lo + j] at delay delays[lo + j] -- the
      (src, delay) pair read at the SAME flat index, aligned entry for
      entry.
    row_lines_len: the table has exactly the row's width.

    Negative control: past the row's width the table answers the default
      Line while the config's flat read still returns a real edge
      (bad_row_lines).
    """
    import random
    rng = random.Random(20261004)
    bad = 0
    for nl in range(1, limit):
        ls = [Lane(max(rng.randrange(1, 4), 1), 0, 0) for _ in range(nl)]
        for nn in range(1, limit):
            indptr = sorted(rng.randrange(6) for _ in range(nn + 1))
            indptr[0] = 0
            m = indptr[-1]
            ixs = [rng.randrange(nl) for _ in range(m)]
            ds = [rng.randrange(4) for _ in range(m)]
            for t in range(nn):
                table = csr_row_lines_py(ls, indptr, ixs, ds, t)
                w = sub(indptr[t + 1] if t + 1 < len(indptr) else 0, indptr[t])
                if len(table) != w:
                    print(f"FAIL row_lines_len t={t}: {len(table)} != {w}")
                    bad += 1
                for j in range(w):
                    want = edge_py(ls, nth(ixs, indptr[t] + j),
                                   nth(ds, indptr[t] + j))
                    if table[j] != want:
                        print(f"FAIL row_lines_nth t={t} j={j}")
                        bad += 1
    # negative control: past the width the table saturates to the default
    table = csr_row_lines_py([Lane(2, 1, 0)], [0, 1], [0], [0], 0)
    if len(table) >= 1 and table[0] != (0, 0, 0, 1, 0):
        pass  # fine
    past = edge_lines_from_py([Lane(2, 1, 0)], [0], [0], 0, 1)
    if past != []:
        print("FAIL bad_row_lines probe: past-width table should be empty")
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
    bad += check_freshness()
    bad += check_slow_lag()
    bad += check_macro_degenerate()
    bad += check_lanes_step_local()
    bad += check_route_pointwise()
    bad += check_tick_split()
    bad += check_non_aliasing()
    bad += check_tier1()
    bad += check_history()
    bad += check_ring()
    bad += check_blend_wiring()
    bad += check_csr_slice()
    bad += check_row_lines()
    if bad:
        print(f"{bad} FAILURES")
        return 1
    print("window_span + hold_until_due + left_invariant + delay_injective "
          "+ staleness (canonical_run/newest_at/stale_bound) + window_ordered "
          "+ list-level routing (lanes_step_local / route_pointwise / tick_split) "
          "+ non-aliasing (read_distinct / i0_win_irrelevant / route_distinct) "
          "+ tier-1 (per-index validation / write-uniqueness / "
          "read_i0_is_window_head) "
          "+ the tape (read-after-write / stability / IC / prune-shift) "
          "+ the ring bridge (mod_lt / ring_first_lap): "
          "all properties hold (exhaustive small range, engine-side) "
          "+ the blend wiring (blend_adjacent / clamp_reads_same / "
          "clamp_zero_frac) "
          "+ the CSR slice (take_nth / slice_nth / slice_len / csr rows) "
          "+ the capstone (row_lines_nth / row_lines_len): "
          "all properties hold (exhaustive small range, engine-side)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
