# LAWS_sweep.bend -- the claims for the sweep's parameter routing.
# Every law here has its proof in PROOF_sweep.bend; the gate is
# tests/run_sweep.sh (verdict + the width negative control + the smoke).
#
# Phase 1: Groups 1-3 of SWEEP_LAWS_DESIGN.md -- row routing, fan
# coverage, gather.  Groups 4-5 (the composition contract and the
# parallelism invariance) are a later phase.
#
# Law style follows LAWS_router.bend: binders reused inside a law carry
# `+` (Data only -- a function-typed binder cannot be `+`); witness-carrying
# binders (R.lt_ok / R.le_ok, Type-valued) stay bare and are used once,
# threaded through the proof's go-lemma.
import Base
import ./sweep.bend as S
import ./router.bend as R

# --------------------------------------------------------------------------
# Group 1 -- the row routing: sim k's parameter IS table word k
# --------------------------------------------------------------------------

# the read lands on the head: no off-by-one at the base
law sweep_nth_head:
  for +h: F32
  for +t: List<&2, F32>
  {S.sweep_nth(h <> t, 0n) == h : F32}

# the stride is exactly one row per sim
law sweep_nth_step:
  for +h: F32
  for +t: List<&2, F32>
  for k: Nat
  {S.sweep_nth(h <> t, 1n+k) == S.sweep_nth(t, k) : F32}

# the routing law: the recursive read and the drop+head reference read
# agree, bounded by the witness lt_ok(k, len) -- sim k's parameter is word
# k, and past the end the claim is UNSTATABLE (the witness cannot be
# fabricated).
law sweep_nth_route:
  for +t: List<&2, F32>
  for k: Nat
  for h: R.lt_ok(k, S.sweep_len(t))
  {S.sweep_nth(t, k) == S.sweep_word(t, k) : F32}

# the instance pin (the csr_row_good convention: positive instance laws
# are load-bearing -- they pin the INTENDED reading of the read).  A
# literal 3-sim table routes sims 0, 1, 2 to their own words.
law sweep_route_inst_0:
  {S.sweep_nth(0.5 <> 1.5 <> 2.5 <> Nil{}, 0n) == 0.5 : F32}

law sweep_route_inst_1:
  {S.sweep_nth(0.5 <> 1.5 <> 2.5 <> Nil{}, 1n) == 1.5 : F32}

law sweep_route_inst_2:
  {S.sweep_nth(0.5 <> 1.5 <> 2.5 <> Nil{}, 2n) == 2.5 : F32}

# --------------------------------------------------------------------------
# Group 2 -- the fan coverage: the active lanes are exactly 0 .. n-1
# --------------------------------------------------------------------------

# the single-lane gate, active arm: lane k (k < n) runs f(k) -- the lane's
# OWN run, at the index the caller asked about (the k0 threading in
# fan_lane_go exists so this law is even statable).
law fan_lane_active:
  for n: Nat
  for k: Nat
  for f: Nat -> String
  for h: R.lt_ok(k, n)
  {S.fan_lane(n, k, f) == f(k) : String}

# the single-lane gate, inactive arm: past n the lane contributes "".
# Together with fan_lane_active this pins the activity decider's meaning
# -- active iff k < n -- the spec-level mirror of the real
# `U32.is_lt(k, n_sweep)` gate (the structural decider stands in for the
# U32 primitive, which does not normalise on symbolic args).
law fan_lane_inactive:
  for n: Nat
  for k: Nat
  for f: Nat -> String
  for +h: {Nat.is_le(n, k) == True{} : Bool}
  {S.fan_lane(n, k, f) == "" : String}

# the nth-of-fan law, WIDTH-PINNED: with n <= 8 the active lanes exist in
# the fixed 8-wide fan, and lane k's output IS run k.  BOTH witnesses are
# load-bearing: without lt_ok(k, n) an inactive lane's "" clashes with its
# run; without le_ok(n, 8) an n > 8 sweep claims coverage for lanes the
# fan does not have -- exactly the silent-drop failure mode.  (The width
# witness enters the proof at fan_go's w = 0, a > 0 case: the dropped
# lanes make the claim false there.)
law fan8_exact:
  for +runs: List<&2, String>
  for n: Nat
  for k: Nat
  for hw: R.le_ok(n, 8n)
  for h: R.lt_ok(k, n)
  {S.str_nth(S.fan8(n, runs), k) == S.str_nth(runs, k) : String}

# the inactive arm at the fan level: lane k with n <= k contributes "".
# Holds WITHOUT the width witness -- past the 8 lanes the read defaults to
# "" too, so the fan never invents output for a dropped lane.
law fan8_active:
  for +runs: List<&2, String>
  for n: Nat
  for k: Nat
  for +h: {Nat.is_le(n, k) == True{} : Bool}
  {S.str_nth(S.fan8(n, runs), k) == "" : String}

# --------------------------------------------------------------------------
# Group 3 -- the gather: lane order IS the output order
# --------------------------------------------------------------------------

# the lane-order law: the fan's gathered output equals the SEQUENTIAL
# concatenation of the first n runs -- f(0) ++ ... ++ f(n-1).  A future
# reordering of the fan (or of the ++ chain) breaks this.  The width
# witness is load-bearing here too: with n > 8 the fan drops lanes and the
# sequential side still demands their output.
law fan_gather_order:
  for +runs: List<&2, String>
  for n: Nat
  for hw: R.le_ok(n, 8n)
  {S.gather(S.fan8(n, runs)) == S.seq_gather(n, runs) : String}
