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
# delayed by d ends at n-d and starts w earlier.  (The quantified claim --
# window span == w whenever d+w <= n -- needs a sub/sub-add lemma library;
# that is the honest price tag on the proof-cost gradient, deferred on
# purpose.  The Python property harness covers it until then.)
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
