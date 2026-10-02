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
