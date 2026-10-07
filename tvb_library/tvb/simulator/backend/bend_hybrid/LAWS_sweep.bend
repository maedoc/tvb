# LAWS_sweep.bend -- the claims for the sweep's parameter routing.
# Every law here has its proof in PROOF_sweep.bend; the gate is
# tests/run_sweep.sh (verdict + the width negative control + the smoke).
#
# Phase 1: Groups 1-3 of SWEEP_LAWS_DESIGN.md -- row routing, fan
# coverage, gather.  Phase 2: Group 4 -- the sweep validator (sweep_ok)
# and the composition capstone (sweep_contract); Group 5's
# parallel-vs-sequential claim is phase 1's fan_gather_order.
#
# REMAINING GAP -- none in this family: the JSON sweep ingress landed
# (section below): the schema is COLUMNS (SWEEP_LAWS_DESIGN.md "Refresh
# 2026-10-05"), the total decode is J.json_sweep_decode, the instance
# pins and the capstone are here, and the patch APPLICATION (slot 0's
# value into the engine's coupling scale) is the one link left open --
# R.Config carries no scale field, so sw_name_slot pins the name->slot
# INDEX resolution only.
#
# Law style follows LAWS_router.bend: binders reused inside a law carry
# `+` (Data only -- a function-typed binder cannot be `+`); witness-carrying
# binders (R.lt_ok / R.le_ok, Type-valued) stay bare and are used once,
# threaded through the proof's go-lemma.
import Base
import ./sweep.bend as S
import ./router.bend as R
import ./json_ingest.bend as J

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

# --------------------------------------------------------------------------
# the JSON SWEEP INGRESS (SWEEP_LAWS_DESIGN.md's remaining gap, closed)
# --------------------------------------------------------------------------
# Schema (COLUMNS -- the TVB sweep API's orientation,
# backend.sweep(params={"coupling_scale": [v0, ..]})):
#   {"sweep_names":["coupling_scale"],"sweep_cols":[[2000,2100]]}
# names as a string list, cols as array-of-arrays (the projs shape the
# config parser already handles); a JSON number is the value SCALED BY
# 1e6 (the job-file convention -- Bend has no float bit-reinterpretation;
# J.sw_f32_of divides back into the F32 the table spec consumes).  The
# decode J.json_sweep_decode is TOTAL: garbage decodes to the empty sweep.

# the transcription pin (the csr_row_good / json_decode_instance
# convention): the literal decode IS the intended table -- names in list
# order, cols in list order, each column's values in sim order.
law json_sweep_instance:
  {J.json_sweep_decode("{\"sweep_names\":[\"coupling_scale\"],\"sweep_cols\":[[2000,2100]]}")
     == J.JSw{"coupling_scale" <> Nil{},
              (J.sw_f32_of(2000n) <> J.sw_f32_of(2100n) <> Nil{}) <> Nil{}}
   : J.JSw}

# keys in REVERSE order, whitespace, a second column: the same table --
# key order does not matter (the json config ingress's property)
law json_sweep_instance_shuffled:
  {J.json_sweep_decode("{ \"sweep_cols\" : [ [ 2000 ] , [ 3000 ] ] , \"sweep_names\" : [ \"coupling_scale\" ] }")
     == J.JSw{"coupling_scale" <> Nil{},
              (J.sw_f32_of(2000n) <> Nil{}) <> (J.sw_f32_of(3000n) <> Nil{}) <> Nil{}}
   : J.JSw}

# garbage decodes to the empty sweep -- the total-decode pin
law json_sweep_garbage:
  {J.json_sweep_decode("zz not json") == J.JSw{Nil{}, Nil{}} : J.JSw}

# the assembled row table's length IS the decoded sim count (the first
# column's length) -- the bridge from the validator's width conjunct to
# the fan the capstone's result half quantifies over
law sw_cols_rows_len:
  for +cols: List<&2, List<&2, F32>>
  {S.rows_len(S.cols_rows(cols)) == S.cols_ns(cols) : Nat}

# the ingress gate ACCEPTS a well-formed sweep against a good shared
# config: one name, one column of two scaled values -- names/cols
# consistent, two assembled rows (<= 8 lanes), one field per row, R.ok.
# Stated over the literal DECODED table (the transcription decode is
# pinned by json_sweep_instance; the BendTT kernel keeps F32 primitive
# applications opaque, so an equation that must normalise THROUGH a
# decoded column is outside --verdict's reach -- the t_rlen_dec probe).
law json_sweep_valid_instance:
  {J.sw_valid(J.JSw{"coupling_scale" <> Nil{},
                    (J.sw_f32_of(1000000n) <> J.sw_f32_of(2000000n) <> Nil{}) <> Nil{}},
              R.Config{1n <> 2n <> Nil{}, R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{}, 4n})
     == True{} : Bool}

# the ingress gate REJECTS ragged columns (a short column's missing sims
# would assemble 0.0-default fields -- the silent-garbage-parameter mode)
law json_sweep_valid_ragged:
  {J.sw_valid(J.JSw{"a" <> "b" <> Nil{},
                    (J.sw_f32_of(1000000n) <> J.sw_f32_of(2000000n) <> Nil{})
                      <> (J.sw_f32_of(3000000n) <> Nil{}) <> Nil{}},
              R.Config{1n <> 2n <> Nil{}, R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{}, 4n})
     == False{} : Bool}

# THE JSON SWEEP CONTRACT -- the ingress capstone (the json_read_fresh
# analog, quantified over ALL strings): for every string s whose decoded
# sweep PASSES the ingress validator (names/cols consistent, then
# sweep_rows_ok on the assembled row table -- width <= 8 lanes, row
# shape, shared config ok), the sweep contract's three halves hold per
# in-bounds sim i and per projection j of the shared config:
#   (a) PARAMS IN: sim i's field j IS column j's value i -- the assembled
#       row routes the named columns (col_to_row instantiated at the
#       decoded table);
#   (b) RESULTS OUT: lane i's output IS run i in the fixed 8-wide fan
#       (fan8_exact, the width witness derived from the validator through
#       sw_cols_rows_len);
#   (c) ROUTING CLEAN: the shared config's routing contract at
#       projection j (the PR.routing_contract_at bridge, R.ok derived
#       from the validator).
# The triple is sweep_contract's pair-equality shape.  The flat-table
# capstone's param half is the ONE-WORD read, so the multi-param table's
# param half goes through col_to_row -- that composition is what this law
# pins; (b) and (c) are sweep_contract's halves verbatim.
law json_sweep_contract:
  for +s: String
  for +c: R.Config
  for +runs: List<&2, String>
  for +tk: Nat
  for +i: Nat
  for +j: Nat
  for +h: {J.sw_valid(J.json_sweep_decode(s), c) == True{} : Bool}
  for hi: R.lt_ok(i, S.cols_ns(J.sw_cols(J.json_sweep_decode(s))))
  for hj: R.lt_ok(j, R.projs_len(R.cfg_projs(c)))
  {(S.sweep_nth(S.col_row(J.sw_cols(J.json_sweep_decode(s)), i), j),
    S.str_nth(S.fan8(S.cols_ns(J.sw_cols(J.json_sweep_decode(s))), runs), i),
    S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j))
   ==
   (S.sweep_nth(S.col_nth(J.sw_cols(J.json_sweep_decode(s)), j), i),
    S.str_nth(runs, i),
    True{})
   : F32 & (String & Bool)}

# --------------------------------------------------------------------------
# the name->slot field map
# --------------------------------------------------------------------------

# the lookup law (instance-pinned): a column NAMED "coupling_scale"
# patches the coupling-scale slot (slot 0) -- the resolution goes through
# the NAME at the column's position k in the sweep_names list, so the
# patch follows the name, not the position.  The patch APPLICATION (slot
# 0's value into the engine's coupling scale) is the remaining link:
# R.Config carries no scale field, the slot index is the pinned interface.
law sw_name_slot:
  for +names: List<&2, String>
  for k: Nat
  for +h: {S.str_nth(names, k) == "coupling_scale" : String}
  {J.sw_slot(names, k) == 0n : Nat}

# the unknown-name arm: a name the slot table does not know lands on the
# junk slot -- it patches nothing (and a past-the-end index reads "" and
# lands there too)
law sw_name_slot_unknown:
  for +names: List<&2, String>
  for k: Nat
  for +h: {S.str_nth(names, k) == "io_gain" : String}
  {J.sw_slot(names, k) == 9n : Nat}

# --------------------------------------------------------------------------
# P2 -- the CONNECTOME SWEEP: per-sim CSR payloads over a shared shape
# --------------------------------------------------------------------------
# The sweep row gains a STRUCTURAL payload: a per-sim CSR with the SAME
# indptr/indices for every sim (fixed node count, fixed edge layout -- no
# model sweeps) and VARYING per-edge weights and delays.  The table is a
# `List<&2, S.CsrPay>` -- one payload RECORD per sim (the representation
# choice, documented in sweep.bend); the shared shape rides as validator
# arguments.  A row's CSR is R.Csr{shared indptr, shared indices, row's
# delays} (S.pay_csr) -- the object the router's csr_ok machinery reads.

# the literal connectome sweep the instance laws pin (the csr_row_good
# convention): 2 nodes, a shared 2-edge shape -- indptr [0,1,2], sources
# [0,1] -- and TWO per-sim payloads: sim 0 weights [0.1, 0.2] delays
# [0, 1], sim 1 weights [0.3, 0.4] delays [2, 0].  Same shape, different
# values: exactly the identical-node-count sweep.
def CS_INDPTR() -> List<&2, Nat>:
  0n <> 1n <> 2n <> Nil{}

def CS_IXS() -> List<&2, Nat>:
  0n <> 1n <> Nil{}

def CS_PAY_0() -> S.CsrPay:
  S.CsrPay{0.1 <> 0.2 <> Nil{}, 0n <> 1n <> Nil{}}

def CS_PAY_1() -> S.CsrPay:
  S.CsrPay{0.3 <> 0.4 <> Nil{}, 2n <> 0n <> Nil{}}

def CS_PAYS() -> List<&2, S.CsrPay>:
  CS_PAY_0() <> CS_PAY_1() <> Nil{}

# the shared config the validator instances run against: 2 lanes
# (the 2 nodes), 1 projection, horizon 4 -- R.ok-approved (the
# json_sweep_valid_instance config)
def CS_CONFIG() -> R.Config:
  R.Config{1n <> 2n <> Nil{}, R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{}, 4n}

# the row routing for the structural payload: sim i's payload (weights
# AND delays together) IS row i -- the sweep_row_nth analog at the CSR
# level.  The recursive read and the drop+head reference read agree,
# bounded by lt_ok(i, npays); past the end the claim is UNSTATABLE (the
# witness cannot be fabricated).
law sweep_csr_route:
  for +pays: List<&2, S.CsrPay>
  for i: Nat
  for h: R.lt_ok(i, S.pays_len(pays))
  {S.pay_nth(pays, i) == S.pay_ref(pays, i) : S.CsrPay}

# the instance pins: the literal 2-sim connectome sweep routes sim 0 and
# sim 1 to their OWN payloads -- weights and delays together.
law sweep_csr_route_inst_0:
  {S.pay_nth(CS_PAYS(), 0n) == CS_PAY_0() : S.CsrPay}

law sweep_csr_route_inst_1:
  {S.pay_nth(CS_PAYS(), 1n) == CS_PAY_1() : S.CsrPay}

# the SHARED SHAPE law: every row's payload is the same length as the
# shared edge layout -- the identical-node-count assumption as a
# validator conjunct, inverted per row (the sweep_rows_shape_nth
# pattern: the every-row fold instantiated at the row the fan routes).
# The bounds witness is load-bearing: past the table the payload reads
# empty (0 edges) and the claim would overreach.
law sweep_csr_shape_shared:
  for +pays: List<&2, S.CsrPay>
  for +ixs: List<&2, Nat>
  for +h: {S.cs_shape_ok(pays, R.nats_len(ixs)) == True{} : Bool}
  for i: Nat
  for hi: R.lt_ok(i, S.pays_len(pays))
  {S.pay_shape_ok(S.pay_nth(pays, i), R.nats_len(ixs)) == True{} : Bool}

# the per-row csr_ok law: EVERY row's CSR -- the shared indptr/indices
# with the row's delays -- passes the router's R.csr_ok (the
# sweep_valid_nth pattern over the router's connectome validation).  The
# node count and horizon come from the shared config.
law sweep_csr_valid_nth:
  for +indptr: List<&2, Nat>
  for +ixs: List<&2, Nat>
  for +pays: List<&2, S.CsrPay>
  for +c: R.Config
  for +h: {S.sweep_csr_ok(indptr, ixs, pays, c) == True{} : Bool}
  for i: Nat
  for hi: R.lt_ok(i, S.pays_len(pays))
  {R.csr_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
            S.pay_csr(indptr, ixs, S.pay_nth(pays, i))) == True{} : Bool}

# the validator's and-elimination family (the section-6 pattern) --
# sweep_csr_ok is a four-deep nested and: width /\ (shape /\ (csr_ok-fold
# /\ R.ok)), so each half eliminates down the right spine.
law sweep_csr_ok_width:
  for +indptr: List<&2, Nat>
  for +ixs: List<&2, Nat>
  for +pays: List<&2, S.CsrPay>
  for +c: R.Config
  for +h: {S.sweep_csr_ok(indptr, ixs, pays, c) == True{} : Bool}
  {Nat.is_le(S.pays_len(pays), 8n) == True{} : Bool}

law sweep_csr_ok_shape:
  for +indptr: List<&2, Nat>
  for +ixs: List<&2, Nat>
  for +pays: List<&2, S.CsrPay>
  for +c: R.Config
  for +h: {S.sweep_csr_ok(indptr, ixs, pays, c) == True{} : Bool}
  {S.cs_shape_ok(pays, R.nats_len(ixs)) == True{} : Bool}

law sweep_csr_ok_csr:
  for +indptr: List<&2, Nat>
  for +ixs: List<&2, Nat>
  for +pays: List<&2, S.CsrPay>
  for +c: R.Config
  for +h: {S.sweep_csr_ok(indptr, ixs, pays, c) == True{} : Bool}
  {S.cs_rows_csr_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
                    indptr, ixs, pays) == True{} : Bool}

law sweep_csr_ok_cfg:
  for +indptr: List<&2, Nat>
  for +ixs: List<&2, Nat>
  for +pays: List<&2, S.CsrPay>
  for +c: R.Config
  for +h: {S.sweep_csr_ok(indptr, ixs, pays, c) == True{} : Bool}
  {R.ok(c) == True{} : Bool}

# the positive validator pin (instance laws are load-bearing): the
# literal 2-sim connectome sweep PASSES the validator against the good
# shared config -- two payloads of the 2-edge shape, both CSRs csr_ok
# (sources < 2 lanes, delays < horizon 4), width <= 8.
law sweep_csr_ok_instance:
  {S.sweep_csr_ok(CS_INDPTR(), CS_IXS(), CS_PAYS(), CS_CONFIG()) == True{} : Bool}

# THE CONNECTOME-SWEEP CONTRACT -- the composition capstone: a VALIDATED
# connectome sweep, at any in-bounds sim i, routes row i's payload to
# sim i (the CsrPay equality) AND row i's CSR passes the router's
# connectome validation AND row i's payload is in the shared shape --
# the sweep's connectivity is provably in-shape and in-bounds per sim.
# The three halves are heterogeneous (CsrPay / Bool / Bool), so the
# Type-level conjunction is the right-nested pair equality -- the
# sweep_contract shape one level down.
law sweep_csr_contract:
  for +indptr: List<&2, Nat>
  for +ixs: List<&2, Nat>
  for +pays: List<&2, S.CsrPay>
  for +c: R.Config
  for +h: {S.sweep_csr_ok(indptr, ixs, pays, c) == True{} : Bool}
  for +i: Nat
  for hi: R.lt_ok(i, S.pays_len(pays))
  {(S.pay_nth(pays, i),
    R.csr_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
             S.pay_csr(indptr, ixs, S.pay_nth(pays, i))),
    S.pay_shape_ok(S.pay_nth(pays, i), R.nats_len(ixs)))
   ==
   (S.pay_ref(pays, i), True{}, True{})
   : S.CsrPay & (Bool & Bool)}

# --------------------------------------------------------------------------
# P3b -- the STOCHASTIC SEEDS (SWEEP_LAWS_DESIGN.md, priority P3): sim i's
# noise stream is seeded by the seed column's element i.
#
# DESIGN CHOICE (documented in sweep.bend): the by-construction assignment
# -- the fan's seeds are seed_row(base, n) = [base+0 .. base+n-1], the
# column the engine BUILDS -- so distinctness is ADD-INJECTIVITY
# (seed_distinct), not a column hypothesis.  A general (e.g. JSON-supplied)
# seed column is still validated: sweep_seed_ok's distinctness fold
# (seeds_unique, the router's writes_unique/ok_no_clash pattern) rejects a
# duplicate pair at load time (bad/bad_seed.bend), and seeds_distinct_nth
# pins the per-index form.
# --------------------------------------------------------------------------

# the read lands on the head: no off-by-one at the base
law seed_nth_head:
  for +h: Nat
  for +t: List<&2, Nat>
  {S.seed_nth(h <> t, 0n) == h : Nat}

# the stride is exactly one sim per seed
law seed_nth_step:
  for +h: Nat
  for +t: List<&2, Nat>
  for k: Nat
  {S.seed_nth(h <> t, 1n+k) == S.seed_nth(t, k) : Nat}

# the seed routing law: the recursive read and the drop+head reference read
# agree, bounded by the witness lt_ok(i, |seeds|) -- sim i's seed IS seed
# column element i; past the end the claim is UNSTATABLE (the witness
# cannot be fabricated).
law seed_route:
  for +seeds: List<&2, Nat>
  for i: Nat
  for h: R.lt_ok(i, R.nats_len(seeds))
  {S.seed_nth(seeds, i) == S.seed_ref(seeds, i) : Nat}

# the instance pins (the sweep_route_inst convention): a literal 3-sim
# seed column routes sims 0, 1, 2 to their own seeds.
law seed_route_inst_0:
  {S.seed_nth(100n <> 200n <> 300n <> Nil{}, 0n) == 100n : Nat}

law seed_route_inst_1:
  {S.seed_nth(100n <> 200n <> 300n <> Nil{}, 1n) == 200n : Nat}

law seed_route_inst_2:
  {S.seed_nth(100n <> 200n <> 300n <> Nil{}, 2n) == 300n : Nat}

# the BY-CONSTRUCTION assignment: the built seed column's element i IS
# base + i -- the construction the distinctness claim rides on
# (seed_row(base, n) = [base+0 .. base+n-1]).
law seed_row_nth:
  for +base: Nat
  for n: Nat
  for i: Nat
  for h: R.lt_ok(i, n)
  {S.seed_nth(S.seed_row(base, n), i) == Nat.add(base, i) : Nat}

# SEED DISTINCTNESS, by construction: two DISTINCT sims never share a
# seed.  For the built column this is add-injectivity -- base + i and
# base + j differ whenever i < j (the delay_injective analog over the
# increment instead of the saturating sub).  No column hypothesis: the
# construction IS the disjointness argument.
law seed_distinct:
  for +base: Nat
  for i: Nat
  for j: Nat
  for +h: {Nat.is_lt(i, j) == True{} : Bool}
  {Nat.is_ne(Nat.add(base, i), Nat.add(base, j)) == True{} : Bool}

# THE REPRODUCIBILITY CLAIM: the seed routing is a PURE function of the
# column -- a rerun of the same sweep routes the same seed to the same
# sim.  Determinism itself comes from purity (a Bend function evaluates
# the same way on every call; the fan consumes the column, never mutates
# it); what the law PINS is the routing: both the fan's read AND a
# rerun's read land on the same reference element, so the seed sim i runs
# with is a function of the validated column alone.
law seed_deterministic:
  for +seeds: List<&2, Nat>
  for +i: Nat
  for +hib: {Nat.is_le(Nat.add(i, 1n), R.nats_len(seeds)) == True{} : Bool}
  {(S.seed_nth(seeds, i), S.seed_nth(seeds, i))
     == (S.seed_ref(seeds, i), S.seed_ref(seeds, i))
   : Nat & Nat}

# --------------------------------------------------------------------------
# the seed validator (sweep_ok's seed half): width /\ distinct /\ R.ok.
# The three and-elimination halves:
# --------------------------------------------------------------------------

law sweep_seed_ok_width:
  for +seeds: List<&2, Nat>
  for +c: R.Config
  for +h: {S.sweep_seed_ok(seeds, c) == True{} : Bool}
  {Nat.is_le(R.nats_len(seeds), 8n) == True{} : Bool}

law sweep_seed_ok_distinct:
  for +seeds: List<&2, Nat>
  for +c: R.Config
  for +h: {S.sweep_seed_ok(seeds, c) == True{} : Bool}
  {S.seeds_unique(seeds) == True{} : Bool}

law sweep_seed_ok_cfg:
  for +seeds: List<&2, Nat>
  for +c: R.Config
  for +h: {S.sweep_seed_ok(seeds, c) == True{} : Bool}
  {R.ok(c) == True{} : Bool}

# the positive validator pin (instance laws are load-bearing): the literal
# 2-sim seed column [100, 200] PASSES -- width 2 <= 8, the pair distinct,
# the shared config ok (the P2 connectome sweep's CS_CONFIG).
# the literal seed column the validator pins run against (the
# csr_row_good convention: named defs, one reading)
def SEEDS() -> List<&2, Nat>:
  100n <> 200n <> Nil{}

law sweep_seed_ok_instance:
  {S.sweep_seed_ok(SEEDS(), CS_CONFIG()) == True{} : Bool}

# the duplicate pin: the distinctness fold REJECTS a repeated seed --
# exactly what the validator exists to catch (two sims aliased onto one
# noise stream).
law seeds_unique_dup:
  {S.seeds_unique(100n <> 100n <> Nil{}) == False{} : Bool}

# the per-index distinctness law (the ok_no_clash pattern): two distinct
# positions of a seed column with the distinctness fold hold DISTINCT
# seeds -- the general-column form of seed_distinct, validator-conditioned
# instead of by-construction.
law seeds_distinct_nth:
  for +seeds: List<&2, Nat>
  for ia: Nat
  for ib: Nat
  for +hltb: {Nat.is_lt(ia, ib) == True{} : Bool}
  for ha: R.lt_ok(ia, R.nats_len(seeds))
  for hb: R.lt_ok(ib, R.nats_len(seeds))
  for +hu: {S.seeds_unique(seeds) == True{} : Bool}
  {Nat.is_ne(R.nats_nth(seeds, ia), R.nats_nth(seeds, ib)) == True{} : Bool}

# THE SEEDED-SWEEP CONTRACT -- the composition capstone (the
# sweep_csr_contract pattern): a VALIDATED seeded sweep, at any in-bounds
# sim i, routes ALL THREE per-sim inputs at once:
#   (a) PARAMS IN: the parameter reaching sim i IS table row i;
#   (b) SEED IN: the seed reaching sim i IS seed column element i;
#   (c) FAN COVERAGE: lane i's output IS run i in the fixed 8-wide fan.
# The three halves are heterogeneous (F32 / Nat / String), so the
# Type-level conjunction is the right-nested pair equality.  The width
# witness for (c) is DERIVED from the parameter validator
# (sweep_ok_width); the two index witnesses are carried in Bool form
# (each feeds TWO consumers: the param read and the fan, so a Type-valued
# witness cannot be duplicated -- the mc_contract idiom).
law sweep_seeded_contract:
  for +t: List<&2, F32>
  for +seeds: List<&2, Nat>
  for +c: R.Config
  for +runs: List<&2, String>
  for +i: Nat
  for +h: {S.sweep_ok(t, c) == True{} : Bool}
  for +hs: {S.sweep_seed_ok(seeds, c) == True{} : Bool}
  for +hkB: {Nat.is_le(Nat.add(i, 1n), S.sweep_len(t)) == True{} : Bool}
  for +hsB: {Nat.is_le(Nat.add(i, 1n), R.nats_len(seeds)) == True{} : Bool}
  {(S.sweep_nth(t, i),
    S.seed_nth(seeds, i),
    S.str_nth(S.fan8(S.sweep_len(t), runs), i))
   ==
   (S.sweep_word(t, i), S.seed_ref(seeds, i), S.str_nth(runs, i))
   : F32 & (Nat & String)}
