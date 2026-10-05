# LAWS_router.bend -- the claims a Bend-native hybrid router must keep true.
#
#   bend PROOF_router.bend            the gate: proofs checked
#   bend PROOF_router.bend --verdict  re-checked by the Lean-proved kernel
#
# The router (router.bend) is a pure Nat tree-traversal: lanes carry the
# multi-dt schedule as counters, projections are routing edges, and a routed
# read is a Line of Nats.  Floats appear only at the leaves, past this file's
# horizon.  Three groups of claims:
#
#   1. the schedule (lane counters): the k=1 degenerate case, the phase
#      invariant (the interpolation fraction is always a proper fraction),
#      monotonicity of publication;
#   2. the read (route_read): every routed Line reads only published samples,
#      the zero-delay clamp is NECESSARY (the unguarded read is always one
#      past the newest), delay is a pure time shift, and the multi-dt read
#      degenerates to the single-dt formula at k=1 -- the golden rule of the
#      multi-dt work, stated as a lemma rather than a golden file;
#   3. the configuration tree: the validators accept a known-good config and
#      reject a bad period, an over-horizon delay and a write collision.
#
# Helper claims (sub_zero, add_zero, ...) are laws of their own because Bend
# has no lemma-in-a-proof; see bendygrad's PORTING_RULES.md rule 11.

import Base
import ./router.bend as R
import ./kernel.bend as K
import ./hist.bend as H

# --------------------------------------------------------------------------
# 0. arithmetic helpers, stated once
# --------------------------------------------------------------------------

law sub_zero:
  for x: Nat
  {Nat.sub(x, 0n) == x : Nat}

law add_zero:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}

law add_succ:
  for a: Nat
  for b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

law le_refl_b:
  for n: Nat
  {Nat.is_le(n, n) == True{} : Bool}

law le_succ_b:
  for n: Nat
  {Nat.is_le(n, 1n+n) == True{} : Bool}

law le_succ_of_le:
  for a: Nat
  for b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(a, 1n+b) == True{} : Bool}

law sub_le_b:
  for n: Nat
  for d: Nat
  {Nat.is_le(Nat.sub(n, d), n) == True{} : Bool}

law lt_succ_b:
  for n: Nat
  {Nat.is_lt(n, 1n+n) == True{} : Bool}


law add_one:
  for x: Nat
  {Nat.add(x, 1n) == 1n+x : Nat}

law add_sub_succ:
  for k: Nat
  for +h: {Nat.is_ge(k, 1n) == True{} : Bool}
  {Nat.add(Nat.sub(k, 1n), 1n) == k : Nat}

law eq_refl_b:
  for n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}

law ne_succ:
  for n: Nat
  {Nat.is_eq(n, 1n+n) == False{} : Bool}

# --------------------------------------------------------------------------
# 1. the schedule
# --------------------------------------------------------------------------

# THE golden rule, counter half: a period-1 lane publishes exactly one sample
# per master tick.  (Generalised over the starting count so the induction
# goes through; the corollary newest == t is n = 0.)
law lane_newest_k1:
  for +t: Nat
  for +n: Nat
  {R.lane_newest(R.steps(t, R.Lane{1n, 0n, n})) == Nat.add(t, n) : Nat}

# stepping never changes a lane's period
law lane_k_preserved:
  for +l: R.Lane
  {R.lane_k(R.step_lane(l)) == R.lane_k(l) : Nat}

# the phase invariant: after ANY number of ticks, `left` stays a valid
# countdown, i.e. the interpolation fraction num/den = (k-1-left)/k is always
# a proper fraction.  This is where the k >= 1 config requirement lives: an
# invalid lane cannot supply the hypothesis.
law lane_phase_bound:
  for t: Nat
  for +l: R.Lane
  for +h: {Nat.is_lt(R.lane_left(l), R.lane_k(l)) == True{} : Bool}
  {Nat.is_lt(R.lane_left(R.steps(t, l)), R.lane_k(l)) == True{} : Bool}

# publication is monotone: a lane never un-publishes
law lane_monotone:
  for +l: R.Lane
  {Nat.is_le(R.lane_newest(l), R.lane_newest(R.step_lane(l))) == True{} : Bool}


# --------------------------------------------------------------------------
# 1b. control flow (the main-loop facts the template states in prose)
# --------------------------------------------------------------------------

# the template's `if t % k == 0` gate, as the carried countdown: a lane
# PUBLISHES exactly when it is due
law due_publishes:
  for +l: R.Lane
  for +h: {Nat.is_eq(R.lane_left(l), 0n) == True{} : Bool}
  {R.lane_newest(R.step_lane(l)) == 1n+R.lane_newest(l) : Nat}

# ... and HOLDS its newest sample exactly when it is not due (the
# zero-order-hold that the temporal-average monitors implicitly average over)
law lane_hold:
  for +l: R.Lane
  for +h: {Nat.is_ne(R.lane_left(l), 0n) == True{} : Bool}
  {R.lane_newest(R.step_lane(l)) == R.lane_newest(l) : Nat}

# due is EXACTLY the publish condition, both directions
law due_iff_publishes:
  for +l: R.Lane
  {Nat.is_eq(R.lane_newest(R.step_lane(l)), 1n+R.lane_newest(l)) == R.lane_due(l) : Bool}

# the countdown evolves as a pure function of (left, k): equal-k lanes can
# never drift apart (decision 10's "identical step grids", for free)
law left_det:
  for +l: R.Lane
  {R.lane_left(R.step_lane(l)) == R.left_next(R.lane_left(l), R.lane_k(l)) : Nat}

# sub_add_cancel: when d <= n, (n - d) + d == n.  The first brick of the
# subtraction library; unlocks the staleness bound (Q1's "up to k-1 ticks
# stale"), delay injectivity and the window span (Q2).
law sub_add_cancel:
  for n: Nat
  for d: Nat
  for +h: {Nat.is_le(d, n) == True{} : Bool}
  {Nat.add(Nat.sub(n, d), d) == n : Nat}

# nb_hybrid's chunking comment, verbatim: "the simulation is correct
# regardless of how many steps a chunk spans" -- because ticks compose.
# This is that comment as a lemma.
law run_segmentable:
  for a: Nat
  for b: Nat
  for +l: R.Lane
  {R.steps(Nat.add(a, b), l) == R.steps(b, R.steps(a, l)) : R.Lane}

# from any countdown position, exactly left+1 ticks take the lane to its
# next publication (and back to the full countdown)
law countdown_publish:
  for left: Nat
  for k: Nat
  for n: Nat
  {R.steps(Nat.add(left, 1n), R.Lane{k, left, n}) == R.Lane{k, Nat.sub(k, 1n), 1n+n} : R.Lane}

# the publish rate: a valid lane publishes EXACTLY once per period, so a
# k-period lane advances newest by 1 across every k master ticks (the
# general form of lane_newest_k1, without any div/mod)
law period_from_init:
  for +k: Nat
  for +n: Nat
  for +h: {Nat.is_ge(k, 1n) == True{} : Bool}
  {R.steps(k, R.Lane{k, Nat.sub(k, 1n), n}) == R.Lane{k, Nat.sub(k, 1n), 1n+n} : R.Lane}

# --------------------------------------------------------------------------
# 1c. monitors (the tavg story: one shared count, ZOH-held averages)
# --------------------------------------------------------------------------
# A1, count_shared: the run has ONE tavg counter, incremented once per master
# tick for ALL subnets (template L1052 -- it is a property of the master
# clock, not of any lane).  Quantified over the lane configuration so the
# claim has teeth: whatever the periods or the NUMBER of lanes, the count
# after t ticks is exactly t + its initial value.  A "fixed" per-subnet
# counter (once per lane, or once per due lane) would make the count depend
# on ks and break this law -- silently changing slow subnets' averages from
# master-time to per-own-step meaning.  The negative control
# bad/bad_count.bend is the per-lane mirror and must be rejected.
law count_shared:
  for t: Nat
  for +ks: List<&2, Nat>
  for +m: R.Mon
  {R.mon_n(R.mon_ticks(t, ks, m)) == Nat.add(t, R.mon_n(m)) : Nat}

# A2, monitor_zoh_average: tavg is the MASTER-TIME average of the ZOH-held
# trajectory.  The publication half is period_from_init (proved above): over
# one period of a lane (period k, k >= 1) exactly one new sample is published,
# the other k-1 ticks hold.  THIS law is the divisor half: the count the
# template divides by (L1259: tavg/n with n = tavg_count) advances by
# exactly k over that same window -- the MASTER span, not the lane's
# publication count.  Conjoined with period_from_init that IS the tavg
# story: a slow subnet's temporal average weights each published sample by
# its hold length in master ticks and divides by the master span.  A
# per-own-step average would divide by the publication count (1 here);
# the k >= 1 hypothesis ties this law to the period it is the divisor OF.
# The float half (sum/k) stays with the kernel (op-order laws); this pins
# the schedule half.  The negative control bad/bad_count.bend claims the
# count does not advance at all (the per-due-lane "fix" for an all-k=1
# network) and must be rejected.
law monitor_zoh_average:
  for +k: Nat
  for +h: {Nat.is_ge(k, 1n) == True{} : Bool}
  for +ks: List<&2, Nat>
  {R.mon_n(R.mon_ticks(k, ks, R.mon_init())) == k : Nat}

# --------------------------------------------------------------------------
# 2. the read
# --------------------------------------------------------------------------

# THE master law: every routed read -- any history depth n, any delay d, any
# fraction, any window -- reads at or behind the newest published sample.
# Freshness is universal because the clamp is part of route_read.
law read_fresh:
  for n: Nat
  for d: Nat
  for num: Nat
  for den: Nat
  for win: Nat
  {Nat.is_le(R.l_i1(R.route_read(n, d, num, den, win)), n) == True{} : Bool}

# the clamp is LOAD-BEARING: the unguarded zero-delay read (i1 = n+1) is
# never fresh.  Stated as "always stale" so the proof is a positive
# induction; bad_router.bend fails to prove the opposite.
law clamp_necessary:
  for n: Nat
  {Nat.is_le(1n+n, n) == False{} : Bool}

# delay is a pure time shift and nothing else
law delay_shift:
  for +n: Nat
  for +d: Nat
  {Nat.sub(n, d) == Nat.sub(Nat.sub(n, 0n), d) : Nat}

# THE golden rule, read half: at k=1 the multi-dt read is the single-dt
# formula i0 = t - d, no interpolation (num = 0).  Replaces the golden-file
# gate "all k=1 must stay bit-for-bit" at the routing level.
law degenerate_read:
  for +t: Nat
  for +d: Nat
  {R.l_i0(R.route_read(R.lane_newest(R.steps(t, R.Lane{1n, 0n, 0n})), d, 0n, 1n, 0n))
      == Nat.sub(t, d) : Nat}

# --------------------------------------------------------------------------
# 3. the configuration tree
# --------------------------------------------------------------------------

# a known-good network: two lanes (periods 1 and 2), two projections writing
# DISTINCT (target, slot) sites, delays inside the horizon
def GOOD() -> R.Config:
  R.Config{1n <> 2n <> Nil{},
           R.Proj{0n, 1n, 3n, 0n, 0n} <> R.Proj{1n, 0n, 1n, 2n, 1n} <> Nil{},
           4n}

# a zero-period lane is rejected
def BAD_PERIOD() -> R.Config:
  R.Config{0n <> 2n <> Nil{},
           R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{},
           4n}

# a delay reaching outside the horizon is rejected
def BAD_DELAY() -> R.Config:
  R.Config{1n <> 2n <> Nil{},
           R.Proj{0n, 1n, 3n, 0n, 0n} <> Nil{},
           2n}

# two projections writing the same (target, slot) are rejected:
# float += is order-dependent, so a collision is observable nondeterminism
def BAD_CLASH() -> R.Config:
  R.Config{1n <> 2n <> Nil{},
           R.Proj{0n, 1n, 1n, 0n, 0n} <> R.Proj{1n, 1n, 1n, 0n, 0n} <> Nil{},
           4n}

law ok_good:
  {R.ok(GOOD()) == True{} : Bool}

law ok_bad_period:
  {R.ok(BAD_PERIOD()) == False{} : Bool}

law ok_bad_delay:
  {R.ok(BAD_DELAY()) == False{} : Bool}

law ok_bad_clash:
  {R.ok(BAD_CLASH()) == False{} : Bool}

# the Q2 anti-alias window, instance level: an average of w source samples
# delayed by d ends at n-d and starts w earlier.  The quantified claim is
# window_span (section 0d); this instance stays as the positive example.
law window_instance:
  {R.route_window(10n, 2n, 3n) == R.Win{5n, 8n} : R.Win}

# --------------------------------------------------------------------------
# 3b. the CSR data structure (per-edge indices and delays)
# --------------------------------------------------------------------------

def GOOD_CSR() -> R.Csr:
  R.Csr{0n <> 2n <> 3n <> Nil{}, 0n <> 1n <> 1n <> Nil{}, 0n <> 1n <> 2n <> Nil{}}

# last indptr (4) != number of indices (3): an edge without a source
def BAD_CSR_COUNT() -> R.Csr:
  R.Csr{0n <> 2n <> 4n <> Nil{}, 0n <> 1n <> 1n <> Nil{}, 0n <> 1n <> 2n <> Nil{}}

# indptr not non-decreasing: row bounds would cross
def BAD_CSR_UNORDERED() -> R.Csr:
  R.Csr{0n <> 2n <> 1n <> 3n <> Nil{}, 0n <> 1n <> 1n <> Nil{}, 0n <> 1n <> 2n <> Nil{}}

# index 5 with only 2 source nodes: out-of-bounds gather
def BAD_CSR_INDEX() -> R.Csr:
  R.Csr{0n <> 2n <> 3n <> Nil{}, 0n <> 5n <> 1n <> Nil{}, 0n <> 1n <> 2n <> Nil{}}

# per-edge delay 9 with horizon 4: two delays would alias onto one slot
# (nb_hybrid's loud failure, as a rejected claim)
def BAD_CSR_DELAY() -> R.Csr:
  R.Csr{0n <> 2n <> 3n <> Nil{}, 0n <> 1n <> 1n <> Nil{}, 0n <> 9n <> 1n <> Nil{}}

law csr_ok_good:
  {R.csr_ok(2n, 4n, GOOD_CSR()) == True{} : Bool}

law csr_ok_bad_count:
  {R.csr_ok(2n, 4n, BAD_CSR_COUNT()) == False{} : Bool}

law csr_ok_bad_unordered:
  {R.csr_ok(2n, 4n, BAD_CSR_UNORDERED()) == False{} : Bool}

law csr_ok_bad_index:
  {R.csr_ok(2n, 4n, BAD_CSR_INDEX()) == False{} : Bool}

law csr_ok_bad_delay:
  {R.csr_ok(2n, 4n, BAD_CSR_DELAY()) == False{} : Bool}

# --------------------------------------------------------------------------
# 4. the leaf layer (kernel.bend): operator order IS the spec
# --------------------------------------------------------------------------

# decision 1's pinned interpolation expression, for SYMBOLIC floats. The
# law is definitional, so a future regrouping -- even one that is
# value-equal in exact arithmetic, like x0 + (x1-x0)*alpha with the
# operands of the mul swapped -- BREAKS it. Rounding order is the
# contract; the negative control bad/bad_blend.bend is exactly that
# regrouping, and must be rejected.
law blend_order:
  for +x0: F32
  for +x1: F32
  for +a: F32
  {K.blend(x0, x1, a) == F32.add(x0, F32.mul(a, F32.sub(x1, x0))) : F32}

# the template's Linear post, term for term: a*wsum + b, no regrouping
law cfun_linear_order:
  for +a: F32
  for +b: F32
  for +w: F32
  {K.cfun_linear(a, b, w) == F32.add(F32.mul(a, w), b) : F32}

# the gather starts from the accumulator (the zeroed coupling scratch)
law gather_nil:
  for +acc: F32
  {K.gather(Nil{}, acc) == acc : F32}

# and folds edges in CSR order: the float sum order is the config's edge
# order. Associativity does not hold in floats, so this order is
# observable -- and pinned.
law gather_cons:
  for +e: K.Edge
  for +t: List<&2, K.Edge>
  for +acc: F32
  {K.gather(e <> t, acc) == K.gather(t, F32.add(acc, F32.mul(K.edge_w(e), K.edge_val(e)))) : F32}

# --------------------------------------------------------------------------
# 0b. the subtraction library (bricks for window_span and staleness_bound)
# --------------------------------------------------------------------------

# (n - d) - w == n - (d + w) when d + w <= n.  The Q2 window span and the
# Q1 staleness bound both need it.  The hypothesis is the structural decider
# le_ok(d + w, n) so the induction destructures it (Bool is_le cannot be
# matched while staying live); the Bool form is le_ok_iff (below).
law sub_sub_add:
  for n: Nat
  for d: Nat
  for w: Nat
  for h: R.le_ok(Nat.add(d, w), n)
  {Nat.sub(Nat.sub(n, d), w) == Nat.sub(n, Nat.add(d, w)) : Nat}

# the decider and the Bool test agree (both directions), stated once
law le_ok_iff:
  for a: Nat
  for b: Nat
  for h: R.le_ok(a, b)
  {Nat.is_le(a, b) == True{} : Bool}

law le_ok_of_b:
  for a: Nat
  for b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {(R.le_ok(a, b) : Type) == Unit : Type}

# n - d <= n for any d (used by the age bound)
law sub_le_self:
  for n: Nat
  for d: Nat
  {Nat.is_le(Nat.sub(n, d), n) == True{} : Bool}

# a <= b and b <= c implies a <= c (le transitivity, Bool form)
law le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for +h1: {Nat.is_le(a, b) == True{} : Bool}
  for +h2: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

# m - (m - w) == w when w <= m (the last window-span brick: hi - lo is a
# difference of window ends sharing the outer n - d, which this cancels)
law sub_sub_cancel:
  for m: Nat
  for w: Nat
  for +h: {Nat.is_le(w, m) == True{} : Bool}
  {Nat.sub(m, Nat.sub(m, w)) == w : Nat}

# w <= n - d whenever d + w <= n (the bridge brick: sub_sub_cancel applied
# to the window needs the span bound on the SHRUNK side of the subtraction)
law le_sub_add:
  for n: Nat
  for d: Nat
  for w: Nat
  for h: R.le_ok(Nat.add(d, w), n)
  {Nat.is_le(w, Nat.sub(n, d)) == True{} : Bool}

# the Q2 anti-alias window span, quantified: whenever d + w <= n, the window
# route_window(n, d, w) returns covers exactly w source samples (its ends
# differ by w).  Replaces the instance-level comment on window_instance,
# which stays as the positive instance.
law window_span:
  for n: Nat
  for d: Nat
  for w: Nat
  for h: R.le_ok(Nat.add(d, w), n)
  {Nat.sub(R.win_hi(R.route_window(n, d, w)), R.win_lo(R.route_window(n, d, w))) == w : Nat}

# n - n == 0 (needed to close the saturated case of sub_sub_cancel)
law sub_self:
  for n: Nat
  {Nat.sub(n, n) == 0n : Nat}

# (1+m) - x == 1 + (m - x) when x <= m (the per-succ step of cancellation)
law sub_succ_l:
  for m: Nat
  for x: Nat
  for +h: {Nat.is_le(x, m) == True{} : Bool}
  {Nat.sub(1n+m, x) == Nat.add(1n, Nat.sub(m, x)) : Nat}

# a <= 1 + a, unconditionally (glue for the cancellation step)
law le_add_one:
  for a: Nat
  {Nat.is_le(a, Nat.add(1n, a)) == True{} : Bool}

# n - 0 == n (sub only reduces on the first argument)
law sub_zero_r:
  for n: Nat
  {Nat.sub(n, 0n) == n : Nat}

# Q1 hold half, quantified: from countdown position left, any t < left+1
# master ticks HOLD the newest sample (ZOH: publishes land exactly on the
# due date, never between).  This is the staleness story's flip side -- a
# k-period lane publishes once per k ticks, so no read is ever more than
# k-1 ticks behind the master; the read half (age <= k-1) follows from this
# plus period_from_init.  Proof: induction on t, peeling one tick each
# step; the countdown shrinks toward the due date, never hitting 0 early.
law hold_until_due:
  for t: Nat
  for +k: Nat
  for left: Nat
  for +n: Nat
  for +h: {Nat.is_lt(t, Nat.add(left, 1n)) == True{} : Bool}
  {R.lane_newest(R.steps(t, R.Lane{k, left, n})) == n : Nat}

# Q1 staleness invariant, countdown half: a countdown that starts inside
# [0, k-1] STAYS there after a step (the countdown never escapes its
# period).  Combined with period_from_init (one publish per period) this
# yields the staleness bound: a k-period lane's newest sample is at most
# k-1 master ticks old -- the countdown upper-bounds the remaining hold.
law left_invariant:
  for left: Nat
  for +k: Nat
  for +h: {Nat.is_le(left, Nat.sub(k, 1n)) == True{} : Bool}
  {Nat.is_le(R.left_next(left, k), Nat.sub(k, 1n)) == True{} : Bool}

# Q1 delay injectivity, quantified: two DISTINCT delays INSIDE the published
# history read two DISTINCT source samples -- the map d |-> n - d is
# injective on d <= n.  This is the routing half of the horizon rule
# (router.bend's csr comment: "horizon >= max(idelay) + 1 ... would alias
# two distinct delays onto the same buffer slot"): with saturating sub the
# aliasing is REAL whenever b > n (n=0 collapses every delay to sample 0,
# the IC fill), so injectivity needs the horizon hypothesis le_ok(b, n) --
# exactly what csr_ok enforces per edge.  Inside the horizon, distinct
# delays stay distinct.
law delay_injective:
  for n: Nat
  for a: Nat
  for b: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  for hb: R.le_ok(b, n)
  {Nat.is_ne(Nat.sub(n, a), Nat.sub(n, b)) == True{} : Bool}

# --------------------------------------------------------------------------
# 6. the ok(cfg)=True law family: the validator implies the shape facts
# --------------------------------------------------------------------------
# The binary dies on ok(cfg) == False, so the interesting routing facts are
# CONDITIONAL on acceptance.  These laws make the "unreachable under ok"
# comments real: from ok(cfg) == True, each conjunct is invertible.  They
# are the bricks for any ok-conditioned routing theorem (e.g. every routed
# read of an accepted config is fresh and inside the horizon).

# and-elimination, both halves
law and_elim_l:
  for a: Bool
  for b: Bool
  for +h: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

law and_elim_r:
  for a: Bool
  for b: Bool
  for +h: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

# ok(cfg) == True decomposes into the three validator conjuncts
law ok_lanes:
  for +c: R.Config
  for +h: {R.ok(c) == True{} : Bool}
  {R.lanes_ok(R.cfg_lanes(c)) == True{} : Bool}

law ok_projs:
  for +c: R.Config
  for +h: {R.ok(c) == True{} : Bool}
  {R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c), R.cfg_projs(c)) == True{} : Bool}

law ok_unique:
  for +c: R.Config
  for +h: {R.ok(c) == True{} : Bool}
  {R.writes_unique(R.cfg_projs(c)) == True{} : Bool}

# the per-edge half: every projection of an accepted config is in shape
law projs_ok_cons:
  for +nlanes: Nat
  for +horizon: Nat
  for +p: R.Proj
  for +ps: List<&2, R.Proj>
  for +h: {R.projs_shape_ok(nlanes, horizon, p <> ps) == True{} : Bool}
  {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool}

law projs_ok_tail:
  for +nlanes: Nat
  for +horizon: Nat
  for +p: R.Proj
  for +ps: List<&2, R.Proj>
  for +h: {R.projs_shape_ok(nlanes, horizon, p <> ps) == True{} : Bool}
  {R.projs_shape_ok(nlanes, horizon, ps) == True{} : Bool}

# the delay conjunct of proj_shape_ok: every accepted projection's delay
# fits the horizon (the csr_ok premise, at the projection level)
law proj_delay_fits:
  for +nlanes: Nat
  for +horizon: Nat
  for +p: R.Proj
  for +h: {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool}
  {Nat.is_le(Nat.add(R.proj_d(p), 1n), horizon) == True{} : Bool}

# the window conjunct of proj_shape_ok: every accepted projection's window
# fits the horizon together with its delay (the anti-alias premise)
law proj_win_fits:
  for +nlanes: Nat
  for +horizon: Nat
  for +p: R.Proj
  for +h: {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool}
  {Nat.is_le(Nat.add(R.proj_d(p), R.proj_win(p)), horizon) == True{} : Bool}

# lanes_ok decomposes: every lane of an accepted config has period >= 1
law lanes_ok_cons:
  for +k: Nat
  for +ks: List<&2, Nat>
  for +h: {R.lanes_ok(k <> ks) == True{} : Bool}
  {Nat.is_ge(k, 1n) == True{} : Bool}

law lanes_ok_tail:
  for +k: Nat
  for +ks: List<&2, Nat>
  for +h: {R.lanes_ok(k <> ks) == True{} : Bool}
  {R.lanes_ok(ks) == True{} : Bool}

# the remaining proj_shape_ok conjuncts: src and tgt are in bounds -- these
# are what makes router.bend's nth_lane default branch ("unreachable under
# ok(cfg)") honest: an accepted projection's src indexes a REAL lane
law proj_src_bounded:
  for +nlanes: Nat
  for +horizon: Nat
  for +p: R.Proj
  for +h: {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool}
  {Nat.is_lt(R.proj_src(p), nlanes) == True{} : Bool}

law proj_tgt_bounded:
  for +nlanes: Nat
  for +horizon: Nat
  for +p: R.Proj
  for +h: {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool}
  {Nat.is_lt(R.proj_tgt(p), nlanes) == True{} : Bool}

# the lookup bricks: nth_lane descends init_lanes structurally, so a
# bounded index lands on a real lane (the default Lane{1,0,0} branch is
# reachable only past the end of the list)
law nth_init_zero:
  for +k: Nat
  for +ks: List<&2, Nat>
  {R.nth_lane(R.init_lanes(k <> ks), 0n) == R.lane_init(k) : R.Lane}

law nth_init_succ:
  for +k: Nat
  for +ks: List<&2, Nat>
  for i: Nat
  {R.nth_lane(R.init_lanes(k <> ks), 1n+i) == R.nth_lane(R.init_lanes(ks), i) : R.Lane}

# --------------------------------------------------------------------------
# 0e. the add/mul rearrangement bricks (for the Q1 staleness capstones)
# --------------------------------------------------------------------------
# Addition commutes.  Needed because run_segmentable peels the FIRST addend
# (steps(a+b) = steps(b, steps(a))) while canonical periods are counted in
# the SECOND (t = q*k + r: peel the whole periods, then the remainder).
# Base has Word.add_comm but not Nat.add_comm; this is that, for Nat.
law add_comm:
  for a: Nat
  for b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

# Addition associates.  With add_comm this lets any sum of periods, counts
# and remainders be regrouped into the shape run_segmentable consumes.
law add_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

# (a + b) - a == b: cancelling the FIRST addend of a sum.  The mirror image
# of sub_add_cancel (which cancels the second under d <= n); this one holds
# unconditionally because a + b >= a always.  It is the arithmetic heart of
# stale_bound: the age t - (publication tick) is the remainder r after
# cancelling the whole periods q*k common to both.
law sub_add_r:
  for a: Nat
  for b: Nat
  {Nat.sub(Nat.add(a, b), a) == b : Nat}

# --------------------------------------------------------------------------
# 1d. the Q1 staleness capstones (the "up to k-1 ticks stale" theorem)
# --------------------------------------------------------------------------
# The prose (ROUTER_EXPLAINER section 6, the parity audit's Q1): a k-period
# lane in macro-first stepping publishes once per k master ticks, so the
# sample a projection reads is never more than k-1 master ticks old.
# LAWS_router:150 promised this as "the staleness bound (Q1's 'up to k-1
# ticks stale') as a theorem" once the subtraction library existed; the
# library (sub_add_cancel, hold_until_due, left_invariant) is now complete,
# so here is the bound, in two halves.
#
# The div/mod-free method: the template would say "newest = t div k" and
# "age = t mod k".  We cannot say that (Nat.div is not in the provable
# world), so the laws are stated over the WITNESS of the decomposition:
# t is quantified as q*k + r with r <= k-1, which every t has and the
# caller produces.  No division, no modulus -- just the recurrence.
#
# Half 1, canonical_run: q WHOLE periods advance the publication count by
# exactly q, from any IC offset n.  This is period_from_init iterated:
# period_from_init is one period; run_segmentable chains them; add_comm
# lines the sum up.  After q*k ticks the lane is back at the canonical
# countdown k-1 -- the phase is a fixed point of the period.
law canonical_run:
  for +k: Nat
  for q: Nat
  for +n: Nat
  for +h: {Nat.is_ge(k, 1n) == True{} : Bool}
  {R.steps(Nat.mul(q, k), R.Lane{k, Nat.sub(k, 1n), n})
     == R.Lane{k, Nat.sub(k, 1n), Nat.add(n, q)} : R.Lane}

# Half 2, newest_at: THE publish count.  At master tick t = q*k + r (r the
# remainder, r <= k-1 so the lane is mid-period) the newest published
# sample is exactly n + q: q publications for the q whole periods, NONE for
# the partial one.  Conjoined with stale_bound this is Q1 complete: the
# count is exact (not just bounded), and the age is the remainder.
# The negative control bad/bad_count.bend guards the monitor's use of this.
law newest_at:
  for +k: Nat
  for q: Nat
  for r: Nat
  for +n: Nat
  for +h: {Nat.is_ge(k, 1n) == True{} : Bool}
  for +hr: {Nat.is_le(r, Nat.sub(k, 1n)) == True{} : Bool}
  {R.lane_newest(R.steps(Nat.add(Nat.mul(q, k), r), R.Lane{k, Nat.sub(k, 1n), n}))
     == Nat.add(n, q) : Nat}

# stale_bound: the AGE half.  At t = q*k + r the newest sample was
# published at tick q*k (sample n+j at tick j*k: the IC at 0, then one per
# period), so its age is exactly the remainder:
#   t - q*k = r <= k-1.
# A slow subnet's input is stale, yes -- but never MORE stale than one
# period minus one, in master ticks.  That is the compensation the
# anti-alias window pays for (explainer: "you cannot take the
# interpolation without paying with the window").
law stale_bound:
  for +k: Nat
  for q: Nat
  for r: Nat
  for +t: Nat
  for +h: {Nat.is_ge(k, 1n) == True{} : Bool}
  for +hr: {Nat.is_le(r, Nat.sub(k, 1n)) == True{} : Bool}
  for +ht: {t == Nat.add(Nat.mul(q, k), r) : Nat}
  {Nat.is_le(Nat.sub(t, Nat.mul(q, k)), Nat.sub(k, 1n)) == True{} : Bool}

# --------------------------------------------------------------------------
# 3b. the window's order (the missing half of the Q2 span law)
# --------------------------------------------------------------------------
# window_span says the window [lo, hi] has exactly w samples when it fits
# (d + w <= n); it does NOT alone say lo <= hi -- a consumer averaging
# over the pair deserves the ends ordered.  Saturating subtraction is
# antitone in the subtrahend: cancelling d from n leaves more the LESS was
# cancelled, so n-(d+w) <= n-d always (the saturating case collapses lo to
# 0, which is <= anything).  Stated under the same fitting witness as
# window_span for symmetry; sub_le_mono (below) is the antitonicity brick.
law window_ordered:
  for n: Nat
  for +d: Nat
  for +w: Nat
  for h: R.le_ok(Nat.add(d, w), n)
  {Nat.is_le(R.win_lo(R.route_window(n, d, w)),
             R.win_hi(R.route_window(n, d, w))) == True{} : Bool}

# the antitonicity brick: cancelling more leaves less-or-equal, inside the
# history (le_ok(b, n) keeps the subtraction honest).  The <= mirror of
# delay_injective's strict sub_lt_mono; window_ordered is its consumer.
law sub_le_mono:
  for n: Nat
  for a: Nat
  for b: Nat
  for h: {Nat.is_le(a, b) == True{} : Bool}
  for hb: R.le_ok(b, n)
  {Nat.is_le(Nat.sub(n, b), Nat.sub(n, a)) == True{} : Bool}

# --------------------------------------------------------------------------
# 3c. the list-level routing laws: many lanes, many projections
# --------------------------------------------------------------------------
# The single-lane laws (lane_hold, due_publishes, ...) pin ONE lane's
# schedule; the single-projection laws (read_fresh, ...) pin ONE read.
# The router's whole tick, though, is lanes_step + route_all over LISTS.
# These three laws lift the pointwise behavior to the list level -- the
# "independently" that every routing argument silently assumes:
#   lanes_step_local:  stepping the list steps lane i, and nothing else
#                      touches lane i -- lanes cannot interact;
#   route_pointwise:   routing a projection list routes projection i from
#                      the same lanes -- projections cannot interact;
#   tick_split:        the sweep loop's chunk safety at the FULL Tick
#                      (lanes AND routed lines): a+b ticks = a then b,
#                      the run_segmentable claim at the router's top level.
#
# Together with writes_unique (in ok) these give the central safety
# statement of the router: the multi-lane tick is EXACTLY the parallel
# composition of per-lane schedules and per-projection reads.

# lane-list locality: stepping the whole list steps each lane
# independently -- the i-th lane of lanes_step(ls) is exactly
# step_lane applied to the i-th lane of ls.  The bounds witness
# (i < lanes_len(ls)) is load-bearing: past the end nth_lane returns the
# default Lane{1,0,0}, whose step is NOT itself -- exactly the
# off-by-one the default branch exists to paper over at runtime.
law lanes_step_local:
  for +ls: List<&2, R.Lane>
  for i: Nat
  for h: R.lt_ok(i, R.lanes_len(ls))
  {R.nth_lane(R.lanes_step(ls), i) == R.step_lane(R.nth_lane(ls, i))  : R.Lane}

# route_all is pointwise: the i-th line of a routed projection list is
# exactly route_proj applied to the i-th projection (against the same,
# untouched lanes).  Bounds witness on the PROJECTION index (the list
# being indexed); the lanes list is only read, so no bound on it.
law route_pointwise:
  for +ls: List<&2, R.Lane>
  for +ps: List<&2, R.Proj>
  for i: Nat
  for h: R.lt_ok(i, R.projs_len(ps))
  {R.nth_line(R.route_all(ls, ps), i)
      == R.route_proj(ls, R.nth_proj(ps, i))  : R.Line}

# chunk safety, full-Tick form: running a+b master ticks equals running
# a, then b, on the whole Tick (lanes and routed lines together).  The
# sweep loop may checkpoint at ANY boundary; this is why.
law tick_split:
  for +ls: List<&2, R.Lane>
  for +ps: List<&2, R.Proj>
  for a: Nat
  for b: Nat
  {R.ticks(Nat.add(a, b), ls, ps)
      == R.ticks(b, R.tick_lanes(R.ticks(a, ls, ps)), ps) : R.Tick}

# --------------------------------------------------------------------------
# 3d. the macro-first degenerate gate: k=1 collapses to the staggered loop
# --------------------------------------------------------------------------
# The macro-first (co-simulation) policy routes slow->fast reads at d=1
# with the interpolation fraction num/den = r/k (phase r within the macro
# window), and fast->slow input as the window average.  The staggered
# policy, at k=1, routes every read as the point read i0 = t - d.
# This law is the GATE between the two: at k=1 the macro-first read --
# d=1, fraction num/den -- IS the staggered point read, because a k=1
# lane has no phase (its countdown is always 0, it is always due, every
# tick publishes) and the interpolation fraction is 0/1 = 0.
#
# In router terms: at k=1, lane_num(l) = (k-1) - left = 0 - 0 = 0, so
# the macro-first read -- route_read at d=1 with the lane's OWN fraction
# -- answers Line{t-1, t, 0, 1, win}: i0 = t-1, which is exactly the
# staggered degenerate_read formula i0 = t-d at d=1.  The fraction the
# macro policy would interpolate with is identically 0: no interpolation
# exists to be missed, and the two orderings read the same samples.
#
# This is the promise of the routing table (explainer section 7): the
# macro-first policy, run on an all-k=1 network, does not drift from
# the staggered policy -- the SAME router state serves both, and the
# golden rule ("all k=1 must stay bit-for-bit") holds at the READ level
# for the co-simulation ordering too, not just the staggered one.
law macro_degenerate:
  for +t: Nat
  for +win: Nat
  {R.l_i0(R.route_read(R.lane_newest(R.steps(t, R.Lane{1n, 0n, 0n})),
                        1n, R.lane_num(R.steps(t, R.Lane{1n, 0n, 0n})),
                        1n, win))
      == Nat.sub(t, 1n) : Nat}

# --------------------------------------------------------------------------
# 3e. the slow-side lag NECESSITY law (the dual of clamp_necessary)
# --------------------------------------------------------------------------
# clamp_necessary is the causality theorem of the STAGGERED policy: a
# zero-delay read asks for sample newest+1, one past everything the
# source has published, so the clamp is not defensive -- it is forced.
#
# This is the mirror for the MACRO-FIRST (co-simulation) policy.  The
# slow lane (k >= 1) integrates FIRST in its macro window; the input it
# consumes is the fast lane's window AVERAGE, whose youngest member is
# at delay d -- sample t-d, emitted on master tick t-d.  Even at the
# freshest legal window position (d = 1, the macro-first signature
# read), the youngest sample the slow lane's input depends on is one
# full macro window old: the window covers ticks (t-d-k, t-d], so the
# input the slow lane sees at tick t is the average over a window
# whose HEAD is t-d-k+1, i.e. at least k ticks behind the head of the
# fast stream.  Two honest claims pin this:
#
#   slow_lag_bound:   the windowed read's freshest member t-d is at
#                     least k-1 ticks behind t whenever the window
#                     fits the history (d + k - 1 <= t):
#                       t - (t-d) = d >= ... no: the AGE of the window's
#                     youngest member is d (its delay), and the window
#                     fitting forces d + k - 1 <= t, i.e. the read is
#                     only legal when the history is long enough to
#                     contain the WHOLE window -- the fitting
#                     hypothesis IS the lag, stated for the head.
#   window_head_age:  the window's OLDEST member (the head of the
#                     average) is d + k - 1 ticks old at tick t --
#                     the slow lane's input is one full window behind
#                     the fast stream, forced by the same fitting.
#
# Together: the slow input's head is d+k-1 old and its tail is d old;
# you cannot shrink either without leaving the history (the clamp)
# or shrinking the window (losing the anti-alias).  The lag is the
# price of the window -- the duality explainer section 6c states in
# prose, now as a pair of laws.

# the tail bound: the windowed read at delay d returns a window whose
# youngest member is t-d, which is exactly d master ticks behind the
# head of the fast stream (t, published at tick t).  This is the AGE
# of the freshest sample the slow lane's input touches -- no fresher
# fast sample participates in a windowed read, ever, whatever the
# schedule does: windowing cannot make input fresher, only older.
law slow_lag_bound:
  for t: Nat
  for d: Nat
  {Nat.is_le(Nat.sub(t, d), t) == True{} : Bool}

# the head bound: the windowed read at delay d, window k, has its OLDEST
# member at route_window's lo = n - (d + k) (window_span proved hi - lo
# = k), which is d + k ticks behind the head of the stream -- provided
# the window fits the history (the same le_ok witness the span law
# uses).  The slow lane's input head is one full window behind.
# THE head bound: the windowed read at (n, d, k) -- the slow lane's
# input at tick n, delay d, window k -- has its OLDEST member at
#   lo = n - (d + k),
# which is EXACTLY d + k ticks behind the head of the stream (sample
# n, published at tick n): the age of the window's head equals the
# full span behind the head, d + k.  This is the necessity half: the
# slow lane's input cannot be fresher than one full window behind,
# because making the head fresher means shrinking d + k, i.e. either
# reading before the window's start (the clamp returns the IC fill)
# or shrinking the window (losing the anti-alias average).  The lag
# is forced by the window's existence, as clamp_necessary's clamp is
# forced by the zero-delay read's causality.
law window_head_age:
  for n: Nat
  for d: Nat
  for k: Nat
  for h: R.le_ok(Nat.add(d, k), n)
  {Nat.add(R.win_lo(R.route_window(n, d, k)), Nat.add(d, k)) == n : Nat}

# --------------------------------------------------------------------------
# 4. the end-to-end freshness laws: the router's whole-tick contract
# --------------------------------------------------------------------------
# The read laws so far are local: read_fresh pins ONE route_read against
# an abstract n; route_pointwise pins that list routing is per-projection;
# lanes_step_local pins that stepping is per-lane.  The kernel's actual
# contract is a COMPOSITION of all three, and no law stated it until now:
#
#   under ok(cfg), at every tick, every routed Line's endpoints point at
#   samples the source lane has already published -- the router never
#   hands the kernel a read the history cannot answer.
#
# Four laws build the ladder, bottom-up:
#   route_all_len    routing is lossless: |route_all(ls, ps)| == |ps|
#                    (no projection silently dropped or duplicated)
#   route_fresh      the pointwise brick: routing projection i reads
#                    only published samples of its OWN source lane
#   read_fresh_tick  the end-to-end claim at ONE tick: after stepping,
#                    every projection's read is fresh
#   read_fresh_ticks the same at t ticks: freshness is tick-invariant
#                    (chunk safety for the freshness property itself)
# plus line_ordered: every routed Line has i0 <= i1 (the interpolation
# interval is well-formed -- the kernel's blend is never inverted).

# routing is lossless: the routed line list has exactly as many lines
# as there are projections.  A dropped projection would be a missing
# coupling edge (a silent no-op); a duplicated one would be a double
# coupling write.  Neither can hide.
law route_all_len:
  for +ls: List<&2, R.Lane>
  for +ps: List<&2, R.Proj>
  {R.lines_len(R.route_all(ls, ps)) == R.projs_len(ps) : Nat}

# the pointwise freshness brick: routing projection i against lanes ls
# reads only published samples -- i1 (the FRESHEST endpoint the kernel
# will touch, clamp included) never exceeds the source lane's newest.
# This is read_fresh specialised to the actual call site: n is not
# abstract, it is lane_newest(nth_lane(ls, proj_src(p))).
law route_fresh:
  for +ls: List<&2, R.Lane>
  for +p: R.Proj
  {Nat.is_le(R.l_i1(R.route_read(R.lane_newest(R.nth_lane(ls, R.proj_src(p))),
                                 R.proj_d(p),
                                 R.lane_num(R.nth_lane(ls, R.proj_src(p))),
                                 R.lane_k(R.nth_lane(ls, R.proj_src(p))),
                                 R.proj_win(p))),
             R.lane_newest(R.nth_lane(ls, R.proj_src(p)))) == True{} : Bool}

# the end-to-end claim at one tick: tick steps the lanes FIRST, then
# routes every projection against the stepped lanes.  Every routed
# line is fresh against its source's POST-TICK newest -- the router
# hands the kernel only samples the (updated) history contains.
law read_fresh_tick:
  for +ls: List<&2, R.Lane>
  for +ps: List<&2, R.Proj>
  for i: Nat
  for h: R.lt_ok(i, R.projs_len(ps))
  {Nat.is_le(R.l_i1(R.nth_line(R.tick_lines(R.tick(ls, ps)), i)),
             R.lane_newest(R.nth_lane(R.lanes_step(ls),
                                       R.proj_src(R.nth_proj(ps, i)))))
      == True{} : Bool}

# freshness is tick-invariant: after t master ticks, every projection's
# routed line is still fresh against its source's newest.  The sweep
# loop's checkpointing cannot break freshness -- the property composes
# exactly as the ticks do (tick_split is the companion composition law).
law read_fresh_ticks:
  for +ls: List<&2, R.Lane>
  for +ps: List<&2, R.Proj>
  for t: Nat
  for i: Nat
  for h: R.lt_ok(i, R.projs_len(ps))
  {Nat.is_le(R.l_i1(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
             R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                       R.proj_src(R.nth_proj(ps, i)))))
      == True{} : Bool}

# the read endpoints are in order: i0 <= i1 in every routed line, so
# the kernel's interpolation interval is never inverted.  (At d=0 the
# clamp sets i0 = i1; at d >= 1 route_read answers i0 = n-(1+dp) and
# i1 = n-dp, and n-(1+dp) <= n-dp always holds -- sub is antitone.)
law line_ordered:
  for +n: Nat
  for +d: Nat
  for +num: Nat
  for +den: Nat
  for +win: Nat
  {Nat.is_le(R.l_i0(R.route_read(n, d, num, den, win)),
             R.l_i1(R.route_read(n, d, num, den, win))) == True{} : Bool}

# --------------------------------------------------------------------------
# 4b. the non-aliasing laws: distinct in-horizon delays never share a slot
# --------------------------------------------------------------------------

# THE Bool->Equal bridge, the gap this batch fills: the decider being True
# means the numbers are actually interchangeable in any goal.  Everything
# downstream that wants to rewrite by an equality of computed Nats goes
# through this brick (route_distinct_src needs it for the source equality).
law eq_of_is_eq:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

# is_le(a+1, b) is is_lt(a, b) under the hood (Cmp shifts by one): the
# bridge brick between the ok(cfg) delay conjunct (stated with the +1:
# d + 1 <= horizon) and delay injectivity's strict hypothesis (d < b).
law lt_of_le_succ:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(Nat.add(a, 1n), b) == True{} : Bool}
  {Nat.is_lt(a, b) == True{} : Bool}

# ok(cfg)'s delay conjunct IS the injectivity premise: an accepted
# projection's delay is strictly inside the history horizon.  Composed with
# read_distinct this turns router.bend's csr comment ("horizon >= max(idelay)
# + 1 ... would alias two distinct delays onto the same buffer slot") into
# a chain of proved laws: ok -> fits_lt -> read_distinct -> no aliasing.
law fits_lt:
  for +nlanes: Nat
  for +horizon: Nat
  for +p: R.Proj
  for +h: {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool}
  {Nat.is_lt(R.proj_d(p), horizon) == True{} : Bool}

# the clamp read never aliases a delayed read: the d=0 branch answers
# i0 = n (the ZOH clamp), a d = 1+dp read answers i0 = n-(1+dp), and
# n-(1+dp) < n holds whenever 1+dp <= n -- i.e. whenever the delayed read
# is inside the horizon at all.  The witness is load-bearing: at n=0 the
# saturated read ALSO answers 0 and the aliasing is real (the IC fill).
law clamp_distinct:
  for n: Nat
  for dp: Nat
  for hb: R.le_ok(Nat.add(1n, dp), n)
  {Nat.is_ne(n, Nat.sub(n, Nat.add(1n, dp))) == True{} : Bool}

# the quantified non-aliasing law: two reads at distinct in-horizon delays
# da < db <= n read distinct i0 samples.  This is delay_injective lifted
# from the index arithmetic to route_read itself -- clamp case included
# (da=0 reads the head n, which only a saturating read could repeat, and
# saturation is excluded by db <= n).
law read_distinct:
  for n: Nat
  for da: Nat
  for db: Nat
  for +num: Nat
  for +den: Nat
  for +win: Nat
  for h: {Nat.is_lt(da, db) == True{} : Bool}
  for hb: R.le_ok(db, n)
  {Nat.is_ne(R.l_i0(R.route_read(n, da, num, den, win)),
             R.l_i0(R.route_read(n, db, num, den, win))) == True{} : Bool}

# the routing half: two projections reading the SAME source lane at
# distinct in-horizon delays route distinct i0s -- they touch disjoint
# source samples, so their coupling contributions are provably not
# reading the same slot of the shared ring.  This is the CSR anti-alias
# rule (router.bend's "would alias two distinct delays onto the same
# buffer slot"), end-to-end through route_proj, at arbitrary lane state
# (num/den/window ride along untouched: the read depends on d only).
# the read index is window-blind: l_i0 does not depend on win at all
# (the averaging window selects which samples the KERNEL averages, never
# which sample the read starts from).  Needed to compare reads from two
# projections that share a source and delays but not windows.
law i0_win_irrelevant:
  for +n: Nat
  for +d: Nat
  for +num: Nat
  for +den: Nat
  for +wa: Nat
  for +wb: Nat
  {R.l_i0(R.route_read(n, d, num, den, wa))
   == R.l_i0(R.route_read(n, d, num, den, wb)) : Nat}

law route_distinct:
  for +ls: List<&2, R.Lane>
  for +pa: R.Proj
  for +pb: R.Proj
  for hsrc: {Nat.is_eq(R.proj_src(pa), R.proj_src(pb)) == True{} : Bool}
  for h: {Nat.is_lt(R.proj_d(pa), R.proj_d(pb)) == True{} : Bool}
  for hb: R.le_ok(R.proj_d(pb),
                 R.lane_newest(R.nth_lane(ls, R.proj_src(pb))))
  {Nat.is_ne(R.l_i0(R.route_read(R.lane_newest(R.nth_lane(ls, R.proj_src(pa))),
                                 R.proj_d(pa),
                                 R.lane_num(R.nth_lane(ls, R.proj_src(pa))),
                                 R.lane_k(R.nth_lane(ls, R.proj_src(pa))),
                                 R.proj_win(pa))),
             R.l_i0(R.route_read(R.lane_newest(R.nth_lane(ls, R.proj_src(pb))),
                                 R.proj_d(pb),
                                 R.lane_num(R.nth_lane(ls, R.proj_src(pb))),
                                 R.lane_k(R.nth_lane(ls, R.proj_src(pb))),
                                 R.proj_win(pb)))) == True{} : Bool}

# --------------------------------------------------------------------------
# 5b. the per-index validation laws: ok(cfg) holds of EVERY element
# --------------------------------------------------------------------------

# an accepted config's projection i (in bounds) satisfies proj_shape_ok:
# the list-level projs_shape_ok fold is not just true of the fold -- every
# reachable projection passes the per-projection validator.  This is what
# lets every downstream ok-conditioned theorem be applied per edge.
law ok_proj_shape_nth:
  for +nlanes: Nat
  for +horizon: Nat
  for +ps: List<&2, R.Proj>
  for i: Nat
  for h: R.lt_ok(i, R.projs_len(ps))
  for hok: {R.projs_shape_ok(nlanes, horizon, ps) == True{} : Bool}
  {R.proj_shape_ok(nlanes, horizon, R.nth_proj(ps, i)) == True{} : Bool}

# every accepted projection's delay is strictly inside the horizon, by
# index -- fits_lt applied at each edge of an accepted projection list.
law ok_fits_nth:
  for +nlanes: Nat
  for +horizon: Nat
  for +ps: List<&2, R.Proj>
  for i: Nat
  for h: R.lt_ok(i, R.projs_len(ps))
  for hok: {R.projs_shape_ok(nlanes, horizon, ps) == True{} : Bool}
  {Nat.is_lt(R.proj_d(R.nth_proj(ps, i)), horizon) == True{} : Bool}

# every lane of an accepted config has period >= 1, by index: the
# monitors/schedule laws that consume lanes_ok can be applied per lane.
law lanes_nth_valid:
  for +ks: List<&2, Nat>
  for i: Nat
  for h: R.lt_ok(i, R.nats_len(ks))
  for hok: {R.lanes_ok(ks) == True{} : Bool}
  {Nat.is_ge(R.nats_nth(ks, i), 1n) == True{} : Bool}

# the CSR per-edge bounds, lifted from the fold: an accepted CSR's edge i
# (in bounds) has its delay inside the horizon and its index inside the
# source-node bounds -- csr_ok's conjuncts hold of every reachable edge,
# not just of the folds.
law csr_nth_delay_fits:
  for +nsrc: Nat
  for +horizon: Nat
  for +c: R.Csr
  for i: Nat
  for h: R.lt_ok(i, R.nats_len(R.csr_delays(c)))
  for hok: {R.csr_ok(nsrc, horizon, c) == True{} : Bool}
  {Nat.is_lt(R.nats_nth(R.csr_delays(c), i), horizon) == True{} : Bool}

law csr_nth_index_bound:
  for +nsrc: Nat
  for +horizon: Nat
  for +c: R.Csr
  for i: Nat
  for h: R.lt_ok(i, R.nats_len(R.csr_indices(c)))
  for hok: {R.csr_ok(nsrc, horizon, c) == True{} : Bool}
  {Nat.is_lt(R.nats_nth(R.csr_indices(c), i), nsrc) == True{} : Bool}

# --------------------------------------------------------------------------
# 5c. the write-uniqueness capstone: ok(cfg) has no double-writes
# --------------------------------------------------------------------------

# a clash is a PAIR condition: proj_clash(a, b) == False plus target
# equality forces the coupling slots apart.  (Contrapositive of the
# constructor: clash = tgt-eq AND tc-eq, so no-clash + tgt-eq gives
# tc-diseq.)
law clash_split:
  for +pa: R.Proj
  for +pb: R.Proj
  for hn: {Bool.not(R.proj_clash(pa, pb)) == True{} : Bool}
  for ht: {Nat.is_eq(R.proj_tgt(pa), R.proj_tgt(pb)) == True{} : Bool}
  {Nat.is_ne(R.proj_tc(pa), R.proj_tc(pb)) == True{} : Bool}

# no_clash extracts at a bounded index: the fold no_clash(a, ps) checks a
# against EVERY element, so element i (in bounds) is clash-free with a.
law no_clash_nth:
  for +pa: R.Proj
  for +ps: List<&2, R.Proj>
  for i: Nat
  for h: R.lt_ok(i, R.projs_len(ps))
  for hnc: {R.no_clash(pa, ps) == True{} : Bool}
  {Bool.not(R.proj_clash(pa, R.nth_proj(ps, i))) == True{} : Bool}

# THE capstone: in an accepted config, two projections writing the SAME
# target lane at distinct indices carry distinct coupling slots -- a
# float += into one slot happens at most once per tick.  This is the
# determinism half of ok's writes_unique conjunct, stated per pair: the
# order-dependent observable (which value lands in the slot) has no
# ambiguity to resolve.
law ok_no_clash:
  for +ps: List<&2, R.Proj>
  for ia: Nat
  for ib: Nat
  for hltb: {Nat.is_lt(ia, ib) == True{} : Bool}
  for ha: R.lt_ok(ia, R.projs_len(ps))
  for hb: R.lt_ok(ib, R.projs_len(ps))
  for hu: {R.writes_unique(ps) == True{} : Bool}
  for ht: {Nat.is_eq(R.proj_tgt(R.nth_proj(ps, ia)),
                     R.proj_tgt(R.nth_proj(ps, ib))) == True{} : Bool}
  {Nat.is_ne(R.proj_tc(R.nth_proj(ps, ia)),
             R.proj_tc(R.nth_proj(ps, ib))) == True{} : Bool}

# --------------------------------------------------------------------------
# 5d. the window-mode agreement: the point read and the window agree
# --------------------------------------------------------------------------

# the point read's start IS the window's head: route_read's i0 and
# route_window's hi are the same sample n-d, so the two read modes
# (interpolated point vs averaged window) never disagree on where the
# averaging interval ends -- the window's newest member is exactly the
# point the 2-point interpolation would read first.  Unconditional:
# at d=0 the clamp sets i0 = n and the window head is n-0 = n.
law read_i0_is_window_head:
  for +n: Nat
  for +d: Nat
  for +num: Nat
  for +den: Nat
  for +win: Nat
  {R.win_hi(R.route_window(n, d, win)) == R.l_i0(R.route_read(n, d, num, den, win)) : Nat}

# --------------------------------------------------------------------------
# 6. the tape: provenance laws for the history (Design A, hist.bend)
# --------------------------------------------------------------------------
# The history joins the router as a proved object.  The tape is the
# simplest absolute-index structure: element i IS the sample at tick i,
# the IC value is the default past the end (the nats_nth convention), and
# these four laws are what every downstream provenance claim composes
# with.  The runtime memory (FTree, flat ring) needs only satisfy these
# laws to BE the tape for the law layer -- the representation-
# independence move that keeps Design B out of every future proof.

# read-after-write: appending v and reading AT THE NEW TOP returns v.
# The numpy gloss: buf[n] = v; buf[n] == v -- for the tape's addressing,
# any length, any depth.  This is the load-bearing write path: whatever
# a lane published this tick IS what a same-tick read at that index sees.
law hist_read_snoc:
  for +xs: List<&2, F32>
  for +v: F32
  for +ic: F32
  {H.hist_read(H.hist_snoc(xs, v), H.hist_len(xs), ic) == v : F32}

# stability: appending at the top never changes any read below the top.
# The numpy gloss: pushing new samples cannot retroactively alter old
# entries -- the property that makes the tape a legal co-simulation
# memory (the sweep loop may checkpoint anywhere; tick_split's partner
# on the data plane).
law hist_snoc_stable:
  for +xs: List<&2, F32>
  for +v: F32
  for +ic: F32
  for i: Nat
  for h: R.lt_ok(i, H.hist_len(xs))
  {H.hist_read(H.hist_snoc(xs, v), i, ic) == H.hist_read(xs, i, ic) : F32}

# IC region: a read at or past the tape's length answers the IC fill,
# never a stale cell -- the engine's buffer pre-fill, as a guarantee.
law hist_read_ic:
  for +xs: List<&2, F32>
  for +ic: F32
  for i: Nat
  for h: R.le_ok(H.hist_len(xs), i)
  {H.hist_read(xs, i, ic) == ic : F32}

# prune-shift: dropping the k oldest samples reindexes the survivors
# exactly -- position i of the pruned tape IS absolute tick i+k, for any
# i below the pruned length.  The numpy gloss: buf2 = buf[k:]; then
# buf2[i] == buf[i+k].  This is the sliding-window law that gives the
# tape the ring's constant memory without the ring's law tax.
# (Unconditional: past the tape's end both sides answer the IC fill, so
# the shift law needs no bounds witness -- the only laws that carry
# witnesses here are stability and IC, where the witness is load-bearing.)
law hist_prune_shift:
  for +xs: List<&2, F32>
  for k: Nat
  for +ic: F32
  for i: Nat
  {H.hist_read(H.hist_drop(xs, k), i, ic)
    == H.hist_read(xs, Nat.add(k, i), ic) : F32}

# --------------------------------------------------------------------------
# 6b. the ring bridge: Design B is the tape inside the fence
# --------------------------------------------------------------------------
# The engine's flat ring (capacity cap, slot i mod cap) is tied back to
# the tape by ONE fence: while the read index stays below the capacity,
# the mod is the identity -- the first lap of the ring IS the tape, slot
# for slot.  This is where the deferred div/mod debt is paid, once; the
# router's proved bounds (every live read lies in [n-horizon, n], and
# ok's shape conjunct will pin horizon <= cap) keep every law-bearing
# read inside the fence, so the wrap never touches a proved claim.

# the fence: below the capacity, the slot address IS the index.
# The numpy gloss: for i in range(cap): ring[i % cap] == ring[i].
law mod_lt:
  for i: Nat
  for +cap: Nat
  for h: R.lt_ok(i, cap)
  {Nat.mod(i, cap) == i : Nat}

# first-lap exactness: a ring read below the capacity IS the tape read
# at the same absolute index -- Design B and Design A agree, slot for
# slot, everywhere the fence holds.  Whatever the tape laws guarantee,
# the ring delivers below the fence.
law ring_first_lap:
  for +xs: List<&2, F32>
  for i: Nat
  for +cap: Nat
  for +ic: F32
  for h: R.lt_ok(i, cap)
  {H.ring_read(xs, i, cap, ic) == H.hist_read(xs, i, ic) : F32}

# --------------------------------------------------------------------------
# 6c. the blend wiring: the interpolation's endpoints are the routed cells
# --------------------------------------------------------------------------
# The kernel leaf turns a routed Line into a value:
#     val = blend(hist[i0], hist[i1], alpha),  alpha = num/den
# The wiring laws pin WHICH tape cells those are.  Two cases, and they
# are the whole story:
#   d >= 1 (in history): the endpoints are ADJACENT ticks, n-d and
#     n-d+1 -- the interpolation never stretches across a gap.
#   d = 0  (the clamp):  both endpoints are the SAME cell (the newest),
#     and the fraction is 0 -- the engine's alpha is 0/1, so the blend
#     degenerates to the newest sample and cannot read one past it.

# adjacency: for an in-history delay d = 1+dp (witness d <= n), the
# routed line's endpoints are exactly one tick apart -- the blend
# interpolates between two ADJACENT published samples.
# The numpy gloss: i1 = i0 + 1, i.e. x1 = hist[n-d+1], x0 = hist[n-d].
# The witness is load-bearing: at n = 0, d = 1 the saturating sub
# collapses both endpoints to 0 and the claim is FALSE (bad_blend_adj).
law blend_adjacent:
  for +n: Nat
  for +dp: Nat
  for +num: Nat
  for +den: Nat
  for +win: Nat
  for h: R.le_ok(Nat.add(1n, dp), n)
  {R.l_i1(R.route_read(n, 1n+dp, num, den, win))
    == Nat.add(R.l_i0(R.route_read(n, 1n+dp, num, den, win)), 1n) : Nat}

# the clamp collapses the endpoints onto the newest cell: both blend
# operands are hist_read(tape, n) -- the zero-delay read IS the newest
# sample, twice, never one past it.
law clamp_reads_same:
  for +tape: List<&2, F32>
  for +n: Nat
  for +num: Nat
  for +den: Nat
  for +win: Nat
  for +ic: F32
  {H.hist_read(tape, R.l_i0(R.route_read(n, 0n, num, den, win)), ic)
    == H.hist_read(tape, R.l_i1(R.route_read(n, 0n, num, den, win)), ic) : F32}

# the clamp zeroes the fraction: the numerator the engine divides is 0,
# so alpha = 0.0 and the blend adds zero times the (bogus) delta.  The
# structural guarantee behind "the clamp read returns the newest value".
law clamp_zero_frac:
  for +n: Nat
  for +num: Nat
  for +den: Nat
  for +win: Nat
  {R.l_num(R.route_read(n, 0n, num, den, win)) == 0n : Nat}

# --------------------------------------------------------------------------
# 6d. the CSR slice laws (Link 3): the edge list folded by gather for
#     target t is exactly the config's rows between indptr[t] and
#     indptr[t+1]
# --------------------------------------------------------------------------
# take_nth: a bounded take is transparent to nth -- reading take(xs, k)
# at i < k is reading xs at i.  The row slice's first half.
law take_nth:
  for +xs: List<&2, Nat>
  for k: Nat
  for i: Nat
  for h: R.lt_ok(i, k)
  {R.nats_nth(R.nats_take(xs, k), i) == R.nats_nth(xs, i) : Nat}

# slice_nth: the HEART of Link 3 -- the i-th edge of target t's slice is
# the config's (lo+i)-th row, i.e. nats_nth(indices, indptr[t] + i).
# The witness lt_ok(i, hi - lo) is load-bearing: past the row's width
# the slice saturates to 0 while the flat read still returns a real row
# (bad_slice).
law slice_nth:
  for +xs: List<&2, Nat>
  for lo: Nat
  for hi: Nat
  for i: Nat
  for h: R.lt_ok(i, Nat.sub(hi, lo))
  {R.nats_nth(R.nats_slice(xs, lo, hi), i)
    == R.nats_nth(xs, Nat.add(lo, i)) : Nat}

# slice_len: the fold's length is bounded by the row's width -- the
# gather never sees MORE edges than the config declares for the row.
law slice_len:
  for +xs: List<&2, Nat>
  for lo: Nat
  for hi: Nat
  {Nat.is_le(R.nats_len(R.nats_slice(xs, lo, hi)), Nat.sub(hi, lo))
    == True{} : Bool}

# the canonical instance, positive and pinned (the csr_ok_good lesson:
# instance laws are load-bearing -- they pin the INTENDED reading).
# GOOD_CSR's row 0 is indices[0..2) = [0, 1], row 1 is indices[2..3) = [1].
law csr_row_good_0:
  {R.csr_row_indices(R.Csr{0n <> 2n <> 3n <> Nil{}, 0n <> 1n <> 1n <> Nil{}, 0n <> 1n <> 2n <> Nil{}}, 0n)
    == 0n <> 1n <> Nil{} : List<&2, Nat>}

law csr_row_good_1:
  {R.csr_row_indices(R.Csr{0n <> 2n <> 3n <> Nil{}, 0n <> 1n <> 1n <> Nil{}, 0n <> 1n <> 2n <> Nil{}}, 1n)
    == 1n <> Nil{} : List<&2, Nat>}

# the delays row slices the SAME bounds: the i-th delay of target t's row
# is the config's (indptr[t] + i)-th delay -- the (src, delay) PAIR a
# gather folds stays aligned, entry for entry.
law csr_row_delays_good_1:
  {R.csr_row_delays(R.Csr{0n <> 2n <> 3n <> Nil{}, 0n <> 1n <> 1n <> Nil{}, 0n <> 1n <> 2n <> Nil{}}, 1n)
    == 2n <> Nil{} : List<&2, Nat>}

# --------------------------------------------------------------------------
# 6e. the end-to-end capstone (Link 4): the routing table of target t's
#     row IS the configured edges, src and delay aligned
# --------------------------------------------------------------------------
# row_lines_nth: the j-th line of target t's routing table is the routed
# read of source indices[lo + j] at delay delays[lo + j], where
# lo = indptr[t].  The witness lt_ok(j, hi - lo) is the row width --
# past it the table saturates (Nil) while the config still has rows
# (bad_row_lines).  This is the composition of the whole ladder:
# csr_ok bounds the flat reads, slice_nth-style addressing picks the
# (src, delay) pair, and route_read (blend_adjacent, clamp laws) makes
# the line.
law row_lines_nth:
  for +ls: List<&2, R.Lane>
  for +c: R.Csr
  for +t: Nat
  for j: Nat
  for h: R.lt_ok(j, Nat.sub(R.csr_row_hi(c, t), R.csr_row_lo(c, t)))
  {R.nth_line(R.csr_row_lines(ls, c, t), j)
    == R.edge(ls,
        R.nats_nth(R.csr_indices(c), Nat.add(R.csr_row_lo(c, t), j)),
        R.nats_nth(R.csr_delays(c), Nat.add(R.csr_row_lo(c, t), j)))
    : R.Line}

# row_lines_len: the routing table has exactly the row's width -- the
# gather folds exactly indptr[t+1] - indptr[t] edges, no more.
law row_lines_len:
  for +ls: List<&2, R.Lane>
  for +c: R.Csr
  for +t: Nat
  {R.lines_len(R.csr_row_lines(ls, c, t))
    == Nat.sub(R.csr_row_hi(c, t), R.csr_row_lo(c, t)) : Nat}

# the positive instance, pinned: GOOD_CSR's row 1 is the single edge
# (src 1, delay 2) read from a 2-lane config -- the exact table the
# gather folds for target 1.
law row_lines_good_1:
  {R.csr_row_lines(R.lane_init(1n) <> R.lane_init(2n) <> Nil{},
                   R.Csr{0n <> 2n <> 3n <> Nil{}, 0n <> 1n <> 1n <> Nil{},
                         0n <> 1n <> 2n <> Nil{}},
                   1n)
    == R.edge(R.lane_init(1n) <> R.lane_init(2n) <> Nil{}, 1n, 2n) <> Nil{}
    : List<&2, R.Line>}

# --------------------------------------------------------------------------
# 7. the cap >= horizon closure: the ring side of the capstone
# --------------------------------------------------------------------------
# The ladder is complete through the routing table (Link 4): target t's
# table IS the configured (src, delay) edges, and each line's blend reads
# the right tape cells (Link 2).  What remained for the ring story is
# COMPOSITION, and this section closes it in three moves:
#
#   ok_cap       the config/engine contract: horizon <= cap.  The engine
#                sizes its ring (hslots = next_pow2(max_delay+1), a power
#                of two for bit-mask addressing) and hands the capacity to
#                the law layer as a parameter, so the conjunct is a
#                companion gate (router.bend's ok_cap), not a Config field
#                -- the config tree stays engine-agnostic.  This is the
#                "cap >= horizon enters ok as a config conjunct" the
#                design record promised, in the shape the layer actually
#                consumes it.
#   read_window  every law-bearing read of an accepted config lies inside
#                [n - horizon, n]: the upper end is read_fresh, the lower
#                end is the delay/window-fits conjuncts of proj_shape_ok
#                composed with sub_antitone (below).  This is the fence
#                condition the ring bridge needs, per read.
#   ring_side    (section 7b) the slot-addressed buffer, the one-lap
#                correspondence theorem, and the composed capstone: for
#                an accepted config over an ok_cap ring, every routed
#                read's ring slot delivers the tape's leaf.
# --------------------------------------------------------------------------

# 7a. the capacity gate and the read-window bound
# --------------------------------------------------------------------------

# the positive instance: GOOD()'s horizon 4 fits the engine's canonical
# ring size for its worst delay, next_pow2(3+1) = 4 -- exactly the hslots
# nb_hybrid would allocate.  cap = horizon is the tightest capacity the
# gate accepts.
law ok_cap_good:
  {R.ok_cap(GOOD(), 4n) == True{} : Bool}

# the negative instance: a ring smaller than the horizon is rejected --
# two ticks one horizon apart would share a slot (bad_ring's aliasing,
# as a config-level failure).
law ok_cap_bad:
  {R.ok_cap(GOOD(), 3n) == False{} : Bool}

# ok_cap inverts to the capacity order, Bool form (the le_ok_iff bridge's
# consumer-side twin: proofs that need the ORDER fact, not the decider).
law ok_cap_le:
  for +c: R.Config
  for +cap: Nat
  for +h: {R.ok_cap(c, cap) == True{} : Bool}
  {Nat.is_le(R.cfg_horizon(c), cap) == True{} : Bool}

# saturating sub is antitone UNCONDITIONALLY: cancelling more leaves
# less-or-equal, saturation included (the saturated side collapses to 0,
# which is <= anything).  sub_le_mono needed the in-history witness to
# keep BOTH sides honest; the lower-bound half only needs the antitonic
# direction, and there the saturation is free.
law sub_antitone:
  for n: Nat
  for a: Nat
  for b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.sub(n, b), Nat.sub(n, a)) == True{} : Bool}

# THE read-window law: every law-bearing read of an accepted projection
# lies at or behind n - horizon.  p's delay fits (d+1 <= horizon) and its
# window fits (d+win <= horizon), so the OLDEST cell any read can name is
# n - (d + win) >= n - horizon: the horizon is exactly the worst-case
# depth.  With read_fresh (i1 <= n) this pins every law-bearing read
# inside [n - horizon, n] -- the window the ring must cover, per read.
law read_window_lo:
  for +n: Nat
  for +nlanes: Nat
  for +horizon: Nat
  for +p: R.Proj
  for +h: {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool}
  {Nat.is_le(Nat.sub(n, horizon),
             Nat.sub(n, Nat.add(R.proj_d(p), R.proj_win(p)))) == True{} : Bool}

# the CSR form of the same bound: every law-bearing CSR read (per-edge
# delay, point reads: win = 0) also lies at or behind n - horizon.  The
# csr_ok delays are strictly inside the horizon, so n - d >= n - horizon
# by antitonicity alone -- the fold's reads are inside the same window.
law csr_window_lo:
  for +n: Nat
  for +nsrc: Nat
  for +horizon: Nat
  for +c: R.Csr
  for +i: Nat
  for +h: {R.csr_ok(nsrc, horizon, c) == True{} : Bool}
  {Nat.is_le(Nat.sub(n, horizon),
             Nat.sub(n, R.nats_nth(R.csr_delays(c), i))) == True{} : Bool}

# a < b implies a <= b (weakening the strict order to the weak one; the
# CSR delays are strictly inside the horizon, and antitonicity consumes
# the weak form).
law le_of_lt:
  for a: Nat
  for b: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

# --------------------------------------------------------------------------
# 7b. the divmod theory: the deferred div/mod debt, paid in full
# --------------------------------------------------------------------------
# The ring correspondence needs three facts about Nat.mod that no existing
# law provides: the remainder is BOUNDED (a slot address is in bounds), the
# modulus is PERIODIC (one lap later the slot address repeats), and the
# first lap is INJECTIVE (two distinct ticks less than a lap apart never
# share a slot -- the no-clobber half of the correspondence).  Nat.divmod's
# go-machine peels ticks from the FRONT with an accumulating state, which
# makes the successor step invisible; the proofs go through a structural
# twin (mm, in PROOF_router.bend) whose wrap-recursion exposes it, tied to
# Nat.mod by one bridge (GO_STATE: the go-machine's remainder IS the
# structural modulus).  After the bridge, everything is plain induction.
# --------------------------------------------------------------------------

# the remainder is inside the ring: every slot address names a real slot.
# The numpy gloss: i % cap is a valid index into a cap-length buffer.
law mod_bound:
  for +n: Nat
  for +cp: Nat
  {Nat.is_le(Nat.mod(n, 1n+cp), cp) == True{} : Bool}

# periodicity: one full lap later, the slot address repeats exactly.
# The numpy gloss: (i + cap) % cap == i % cap -- the ring's whole point.
law mod_period:
  for +n: Nat
  for +cp: Nat
  {Nat.mod(Nat.add(n, 1n+cp), 1n+cp) == Nat.mod(n, 1n+cp) : Nat}

# the positive instance, pinned: 9 mod 4 == 5 mod 4 == 1 (one lap apart).
law mod_period_good:
  {Nat.mod(Nat.add(5n, 4n), 4n) == Nat.mod(5n, 4n) : Nat}

# THE one-lap injectivity: two distinct ticks less than a lap apart NEVER
# share a slot -- a write at i+t (1 <= t < cap) cannot clobber slot
# mod(i, cap).  This is the no-clobber half of the ring correspondence,
# and it is exactly the fact an under-capacity ring violates (bad_cap):
# there, ticks a horizon apart DO share a slot, and the delay aliasing
# the csr comment warns about becomes real.
law mod_inj_lap:
  for +i: Nat
  for +t: Nat
  for +cp: Nat
  for +h1: {Nat.is_le(1n, t) == True{} : Bool}
  for +h2: {Nat.is_le(t, cp) == True{} : Bool}
  {Nat.is_ne(Nat.mod(Nat.add(i, t), 1n+cp), Nat.mod(i, 1n+cp))
     == True{} : Bool}

# --------------------------------------------------------------------------
# 8. THE CONTRACT: the three named capstones (statements; proofs = Phase 2)
# --------------------------------------------------------------------------
# The three contracts the proving phases owe, WRITTEN AND PINNED but
# deliberately COMMENTED OUT -- none is a claim the current file checks,
# because one names functions that do not exist yet (memory_contract's
# Phase-1 ring write path) and one needs an import this file does not
# carry (ingress_contract's json_ingest).  Uncommenting is Phase 2's
# first move, one law at a time, each with its proof def in
# PROOF_router.bend.  Nothing here deletes or weakens any law above: the
# three statements are compositions of already-proved bricks, and their
# role is to pin the SCOPE of the proving phases before any proof is
# written -- the shape of the goal is the contract, and the bricks are
# already on the shelf.

# THE ROUTING CONTRACT.  For every ACCEPTED config, every tick count t,
# every in-bounds projection index i, the routed line of projection i is
#   (a) FRESH: l_i1 <= its source lane's newest sample -- no read sees
#       the future (read_fresh_ticks, the tick-invariant end-to-end law);
#   (b) IN-WINDOW: l_i0 >= newest - horizon -- no read falls off the far
#       end of the history (read_window_lo plus the ok-projection
#       conjuncts -- ok_proj_shape_nth, ok_fits_nth -- lifted to tick
#       state, so the per-projection shape facts hold of the config's
#       OWN projection list at every tick);
#   (c) ORDERED: l_i0 <= l_i1 -- the interpolation interval is never
#       inverted (line_ordered).
# The lanes/projections are tied to the config by equality hypotheses
# (ls == init_lanes(cfg_lanes(c)), ps == cfg_projs(c)) so the tick
# expressions stay short and the claim is exactly about the state a
# caller would run: the config's own lanes, its own projections.  Phase
# 2 proves this by INSTANTIATING existing laws (read_fresh_ticks,
# read_window_lo and line_ordered are already proved); bricks are added
# only where an induction is missing -- the expected gap is the
# window-lo lift from one route_read to the whole-tick state.  At proof
# time the single law may be split into three lemmas (fresh, in-window,
# ordered) plus a conjunction capstone, as the proof file prefers.
# law routing_contract:
#   for +c: R.Config
#   for +ls: List<&2, R.Lane>
#   for +ps: List<&2, R.Proj>
#   for t: Nat
#   for i: Nat
#   for +h: {R.ok(c) == True{} : Bool}
#   for +hls: {ls == R.init_lanes(R.cfg_lanes(c)) : List<&2, R.Lane>}
#   for +hps: {ps == R.cfg_projs(c) : List<&2, R.Proj>}
#   for hb: R.lt_ok(i, R.projs_len(ps))
#   {Bool.and(Nat.is_le(R.l_i1(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
#                       R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
#                                                 R.proj_src(R.nth_proj(ps, i))))),
#       Bool.and(Nat.is_le(Nat.sub(R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
#                                                          R.proj_src(R.nth_proj(ps, i)))),
#                                   R.cfg_horizon(c)),
#                          R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i))),
#                Nat.is_le(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
#                          R.l_i1(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)))))
#    == True{} : Bool}

# THE MEMORY CONTRACT (section 7's promised composed capstone).  For
# every ACCEPTED config c with R.ok_cap(c, cap) == True, over a tape,
# every law-bearing routed read's RING SLOT delivers the tape's leaf:
# the engine's ring holds, at slot s, the sample of the NEWEST tick
# congruent to s mod cap, and law-bearing reads lie in
# [newest - horizon, newest] with horizon <= cap (read_window_lo +
# read_fresh + ok_cap) -- i.e. inside the live window, where the slot
# delivers exactly the tape's sample.  The bricks: the divmod family
# (mod_lt, mod_period, mod_inj_lap) plus Phase 1's WRITE laws.  Note
# which side is which: ring_read as it exists TODAY is the mod-addressed
# tape read -- the SPEC side, whose fence law is ring_first_lap (below
# the capacity, the slot address IS the index); H.ring_of / the ring
# write path is the IMPLEMENTATION side, the correspondence theorem's
# other half -- exactly the Design A / Design B split hist.bend's header
# comment states.  This statement deliberately REFERENCES FUNCTIONS THAT
# DO NOT EXIST YET: H.ring_of is the Phase-1 ring write path, and naming
# it here PINS the API Phase 1 must provide (a tape-to-ring constructor
# the correspondence theorem can tie to ring_read's spec).  The claim is
# stated for i0; the i1 endpoint form is identical (conjoin both at
# proof time if the capstone wants it).
# law memory_contract:
#   for +c: R.Config
#   for +cap: Nat
#   for +tape: List<&2, F32>
#   for +ic: F32
#   for +ls: List<&2, R.Lane>
#   for +ps: List<&2, R.Proj>
#   for t: Nat
#   for i: Nat
#   for +h: {R.ok(c) == True{} : Bool}
#   for +hcap: {R.ok_cap(c, cap) == True{} : Bool}
#   for +hls: {ls == R.init_lanes(R.cfg_lanes(c)) : List<&2, R.Lane>}
#   for +hps: {ps == R.cfg_projs(c) : List<&2, R.Proj>}
#   for hb: R.lt_ok(i, R.projs_len(ps))
#   {H.ring_read(H.ring_of(tape, cap),  # (Phase 1: to be provided)
#                R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)), cap, ic)
#      == H.hist_read(tape, R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)), ic)
#    : F32}

# THE INGRESS CONTRACT.  The same claim as law json_read_fresh
# (LAWS_json.bend section 4, the ingress capstone): for every string s
# whose decoded config PASSES R.ok, every routed read after ANY tick
# count is fresh -- no runtime JSON input can escape the routing
# contract's freshness half.  This statement is ALREADY PROVED (in
# PROOF_json.bend, checked green by tests/run_json.sh); restated here as
# the third named member of the contract family so section 8 is the one
# place the whole contract is legible.  Phase 2 only LINKS it (a rename
# / re-export), it does not re-prove it.  Kept commented because
# LAWS_router.bend does not import json_ingest -- uncommenting requires
# adding `import ./json_ingest.bend as J` here, which is the Phase-2
# move (and the law is checked green in LAWS_json.bend regardless).
# law ingress_contract:  # needs: import ./json_ingest.bend as J
#   for +s: String
#   for +m: Nat
#   for +h: {R.ok(J.json_decode(s)) == True{} : Bool}
#   {J.bumps_fresh(J.lanes_run(m, R.init_lanes(R.cfg_lanes(J.json_decode(s)))),
#                  R.cfg_projs(J.json_decode(s)), 0n) == True{} : Bool}
