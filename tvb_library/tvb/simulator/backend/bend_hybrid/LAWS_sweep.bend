# LAWS_sweep.bend -- the claims for the sweep's parameter routing.
# Every law here has its proof in PROOF_sweep.bend; the gate is
# tests/run_sweep.sh (verdict + the width negative control + the smoke).
#
# Phase 1: Groups 1-3 of SWEEP_LAWS_DESIGN.md -- row routing, fan
# coverage, gather.  Phase 2: Group 4 -- the sweep validator (sweep_ok)
# and the composition capstone (sweep_contract); Group 5's
# parallel-vs-sequential claim is phase 1's fan_gather_order.
#
# REMAINING GAP -- the JSON sweep ingress: the schema is an open design
# question (per-sim rows {"sims": [{..}, ..]} vs per-parameter columns
# {"scale": [..], ..}); the table spec above is agnostic.  Once decided,
# the ingress laws pin it with the json_ingest state-machine pattern
# (total decode: garbage decodes to the empty sweep), the instance pins,
# and a json_sweep_contract quantified over all strings (the
# json_read_fresh analog) composing onto sweep_contract.
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

# --------------------------------------------------------------------------
# Group 4 -- the composition: the sweep validator and the sweep contract
# --------------------------------------------------------------------------

# and-elimination, the width half: a validated sweep's table fits the
# fixed 8-wide fan -- fan8_exact's le_ok(n, 8) witness, promoted to a
# validator conjunct so an n_sweep > 8 sweep is REJECTED, not silently
# truncated (the ok_lanes pattern).
law sweep_ok_width:
  for +t: List<&2, F32>
  for +c: R.Config
  for +h: {S.sweep_ok(t, c) == True{} : Bool}
  {Nat.is_le(S.sweep_len(t), 8n) == True{} : Bool}

# and-elimination, the config half: a validated sweep's SHARED config
# passes the per-sim validator R.ok -- one ok() call covers the whole
# Monte-Carlo batch, since only the swept parameter varies per sim.
law sweep_ok_cfg:
  for +t: List<&2, F32>
  for +c: R.Config
  for +h: {S.sweep_ok(t, c) == True{} : Bool}
  {R.ok(c) == True{} : Bool}

# every in-bounds row of a validated sweep exists (the lt_ok witness is
# exactly that) and is the row the fan routes: lane k's output IS run k,
# with the width witness DERIVED from the validator instead of assumed --
# the lanes_nth_valid pattern (fan8_exact swept through sweep_ok).
law sweep_valid_nth:
  for +t: List<&2, F32>
  for +c: R.Config
  for +runs: List<&2, String>
  for +h: {S.sweep_ok(t, c) == True{} : Bool}
  for k: Nat
  for hk: R.lt_ok(k, S.sweep_len(t))
  {S.str_nth(S.fan8(S.sweep_len(t), runs), k) == S.str_nth(runs, k) : String}

# THE SWEEP CONTRACT -- the Monte-Carlo capstone, ONE claim over the
# triple (param in, result out, routing clean).  For a validated sweep,
# an in-bounds sim i, and ANY projection j of the shared config:
#   (a) PARAMS IN: the parameter reaching sim i IS table row i
#       (sweep_nth_route instantiated);
#   (b) RESULTS OUT: lane i's output IS run i in the fixed 8-wide fan
#       (fan8_exact instantiated, the width witness from sweep_ok_width);
#   (c) ROUTING CLEAN: the shared config's routing contract holds at
#       projection j (Laws.routing_contract instantiated at the shared
#       config -- its conclusion bundle is S.routing_bundle; discharged
#       by the bridge routing_contract_at in PROOF_router.bend).  The sim
#       index i and the projection index j are INDEPENDENT quantifiers:
#       the routing claim is per-projection of the shared config, not
#       tied to the sim.
# The three halves are heterogeneous (an F32 equality, a String equality
# and a Bool bundle), so Bool.and cannot carry them; the Type-level
# conjunction is the pair equality below -- (F32 & (String & Bool)) --
# which holds exactly when every component does.  The bundle expression
# is factored into S.routing_bundle so the law reads as one claim.
law sweep_contract:
  for +t: List<&2, F32>
  for +c: R.Config
  for +runs: List<&2, String>
  for +tk: Nat
  for +i: Nat
  for +j: Nat
  for +h: {S.sweep_ok(t, c) == True{} : Bool}
  for hk: R.lt_ok(i, S.sweep_len(t))
  for hj: R.lt_ok(j, R.projs_len(R.cfg_projs(c)))
  {(S.sweep_nth(t, i),
    S.str_nth(S.fan8(S.sweep_len(t), runs), i),
    S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j))
   ==
   (S.sweep_word(t, i), S.str_nth(runs, i), True{})
   : F32 & (String & Bool)}

# --------------------------------------------------------------------------
# Phase 3 -- the GENERALIZATION (SWEEP_LAWS_DESIGN.md, "Sweep v2")
# --------------------------------------------------------------------------
# A. GENERAL WIDTH: fan_go is the general-width recursion (fan8 =
#    fan_go(8n, n, runs)); the width witness becomes le_ok(n, w) and the
#    fan8 laws are its w = 8 instances.
#
# the nth law at GENERAL width: with n <= w the fan has lane k, and lane
# k's output IS run k.  BOTH witnesses are load-bearing (the fan8_exact
# analysis carries verbatim): without lt_ok(k, n) an inactive lane's ""
# clashes with its run; without le_ok(n, w) an n > w sweep claims coverage
# for lanes the fan does not have -- the silent-drop failure mode.
law fan_exact:
  for +runs: List<&2, String>
  for w: Nat
  for n: Nat
  for k: Nat
  for hw: R.le_ok(n, w)
  for h: R.lt_ok(k, n)
  {S.str_nth(S.fan_go(w, n, runs), k) == S.str_nth(runs, k) : String}

# the gather law at GENERAL width: the gathered fan equals the sequential
# concatenation of the first n runs, for ANY width w that fits n.  The
# demos sweep 20 points -- over the 8-wide fan -- so the real engine needs
# the general statement, not just the w = 8 instance.
law fan_gather_order_gen:
  for +runs: List<&2, String>
  for w: Nat
  for n: Nat
  for hw: R.le_ok(n, w)
  {S.gather(S.fan_go(w, n, runs)) == S.seq_gather(n, runs) : String}

# --------------------------------------------------------------------------
# B. MULTI-PARAM ROWS: the table generalizes to one ROW of parameters per
#    sim (the cs_row / cs_get_row 2-level shape).
# --------------------------------------------------------------------------

# the row-routing law: sim i's parameter row IS row i -- the recursive
# read and the drop+head reference read agree, bounded by lt_ok(i, nrows)
# (the sweep_nth_route pattern at the row level; past the end the claim is
# UNSTATABLE -- the witness cannot be fabricated).
law sweep_row_nth:
  for +rows: List<&2, List<&2, F32>>
  for i: Nat
  for h: R.lt_ok(i, S.rows_len(rows))
  {S.sweep_row(rows, i) == S.sweep_row_ref(rows, i) : List<&2, F32>}

# the field read: row i's field j IS field j -- sweep_nth_route at the
# row's word level (sweep_field IS sweep_nth(row i, ·); the reference read
# is the drop+head sweep_word).  The row witness pins the row exists; the
# field witness pins the field is inside the row.
law sweep_field_nth:
  for +rows: List<&2, List<&2, F32>>
  for i: Nat
  for j: Nat
  for hi: R.lt_ok(i, S.rows_len(rows))
  for hj: R.lt_ok(j, S.sweep_len(S.sweep_row(rows, i)))
  {S.sweep_field(rows, i, j) == S.sweep_word(S.sweep_row(rows, i), j) : F32}

# the row-major ADDRESS brick: row (1+i)'s field j lives at
# w + (i*w + j) -- the mul-distributivity step over the row counter that
# the wire-agreement law recurses through (the divmod family's brick
# pattern; Nat.mul(1n+i, w) reduces to w + i*w, add_assoc regroups).
law flat_addr_step:
  for +i: Nat
  for +w: Nat
  for +j: Nat
  {S.flat_addr(1n+i, w, j) == Nat.add(w, S.flat_addr(i, w, j)) : Nat}

# the row-major WIRE agreement: the closed-form address read and the
# structural skip-rows read agree -- flat[i*w + j] IS row i's field j.
# Unconditional: past-the-end reads default to 0.0 on both sides (a short
# final row and an out-of-range row agree), and the i = 0 base is
# definitional (0*w + j reduces to j).
law flat_nth:
  for +flat: List<&2, F32>
  for +w: Nat
  for i: Nat
  for j: Nat
  {S.flat_at(flat, i, w, j) == S.flat_read(flat, i, w, j) : F32}

# the COLUMN->ROW assembly law: the assembled row's field j IS column j's
# element i -- row i field j == column j's i-th value.  This pins the TVB
# API's orientation: params={"coupling_scale": [v0, ..]} varies the
# parameter ACROSS sims down the column, and the per-sim row is the
# assembly.  Unconditional: past-the-end reads default to 0.0 on both
# sides (a short column and the assembled row agree).
law col_to_row:
  for +cols: List<&2, List<&2, F32>>
  for i: Nat
  for j: Nat
  {S.sweep_nth(S.col_row(cols, i), j) == S.sweep_nth(S.col_nth(cols, j), i) : F32}

# the instance pin (the csr_row_good convention): a literal 2-sim x 2-param
# COLUMN table -- params={"a": [0.5, 1.5], "b": [2.5, 3.5]} -- assembles
# sim 0's row [0.5, 2.5] and sim 1's row [1.5, 3.5]: element i of every
# column, in column order.
law col_row_inst_0:
  {S.col_row((0.5 <> 1.5 <> Nil{}) <> (2.5 <> 3.5 <> Nil{}) <> Nil{}, 0n)
   == 0.5 <> 2.5 <> Nil{} : List<&2, F32>}

law col_row_inst_1:
  {S.col_row((0.5 <> 1.5 <> Nil{}) <> (2.5 <> 3.5 <> Nil{}) <> Nil{}, 1n)
   == 1.5 <> 3.5 <> Nil{} : List<&2, F32>}

# --------------------------------------------------------------------------
# the ROW-TABLE validator: sweep_ok's multi-param generalization -- the
# width conjunct stays at 8 (the current engine), the ROW-SHAPE conjunct
# (every row has exactly wp fields) is new, R.ok on the shared config is
# unchanged.  The three and-elimination halves:
# --------------------------------------------------------------------------

law sweep_rows_ok_len:
  for +rows: List<&2, List<&2, F32>>
  for +wp: Nat
  for +c: R.Config
  for +h: {S.sweep_rows_ok(rows, wp, c) == True{} : Bool}
  {Nat.is_le(S.rows_len(rows), 8n) == True{} : Bool}

law sweep_rows_ok_shape:
  for +rows: List<&2, List<&2, F32>>
  for +wp: Nat
  for +c: R.Config
  for +h: {S.sweep_rows_ok(rows, wp, c) == True{} : Bool}
  {S.rows_shape_ok(rows, wp) == True{} : Bool}

law sweep_rows_ok_cfg:
  for +rows: List<&2, List<&2, F32>>
  for +wp: Nat
  for +c: R.Config
  for +h: {S.sweep_rows_ok(rows, wp, c) == True{} : Bool}
  {R.ok(c) == True{} : Bool}

# the per-row inversion (the sweep_valid_nth / lanes_nth_valid pattern):
# every IN-BOUNDS row of a validated table has exactly wp fields -- the
# every-row fold instantiated at the row the fan routes.  The bounds
# witness is load-bearing: past the table the row reads empty (0 fields),
# and the claim would overreach.
law sweep_rows_shape_nth:
  for +rows: List<&2, List<&2, F32>>
  for +wp: Nat
  for +c: R.Config
  for +h: {S.sweep_rows_ok(rows, wp, c) == True{} : Bool}
  for i: Nat
  for hi: R.lt_ok(i, S.rows_len(rows))
  {Nat.is_eq(S.sweep_len(S.sweep_row(rows, i)), wp) == True{} : Bool}
