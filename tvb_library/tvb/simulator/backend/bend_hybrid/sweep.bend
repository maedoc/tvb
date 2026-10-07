# sweep.bend -- the PURE SPEC of the Monte-Carlo sweep's parameter routing
# (montbrio_sweep.bend's sweep half, mirrorable and provable).
#
# What the real sweep does (montbrio_sweep.bend):
#   - the job file's sweep section is `n_sweep` 4-byte words, one varying
#     F32 per sim; `build_and_run(k, ...)` reads word k of the decoded
#     table (`Array.get(U32, sww, k)`);
#   - the fan is FIXED 8-WIDE (`sweep8`): lane k runs `point(k, in, active)`
#     with `active = U32.is_lt(k, n_sweep)`; inactive lanes cost a match,
#     not a sim, and contribute "";
#   - the outputs concatenate in lane order (the `x ++ y` chain).
#
# The silent-failure mode this layer polices: `n_sweep > 8` DROPS sims
# without any error, because the fan is fixed-width.  The laws
# (LAWS_sweep.bend / PROOF_sweep.bend) make the width bound a REQUIRED
# witness; bad/bad_sweep_width.bend is the negative control.
#
# SPEC SHAPE (the tape/ring convention: the list is the spec, the Array is
# the implementation):
#   - the TABLE is a FLAT `List<&2, F32>` -- one varying parameter per sim,
#     matching the prototype's one-word-per-sim sweep section.  Phase 3
#     adds the 2-LEVEL table `List<&2, List<&2, F32>>` -- one ROW of
#     parameters per sim (the same shape as coupling.bend's `cs`) -- plus
#     the row-major flat wire layout and the COLUMN->ROW assembly (the TVB
#     sweep API is named-key columns: params={"coupling_scale": [v0, ..]}).
#   - the FAN takes the per-lane runs as a `List<&2, String>` -- a run
#     FUNCTION `f: Nat -> String` cannot be shared 8 ways (Bend is affine
#     and a function is not Data, so an 8-lane fan cannot take `f`), which
#     mirrors the real sweep8 exactly: it shares `in: In` -- Data -- across
#     lanes and never passes a function.  The single-lane gate `fan_lane`
#     DOES take `f: Nat -> String` (one use per call) and carries the
#     gate's laws; `fan8` carries the fan-shape laws over the Data table.
#   - the activity decider is the STRUCTURAL Nat mirror of the real
#     `U32.is_lt(k, n)` gate (U32 primitives do not normalise on symbolic
#     args, so the spec decides `k < n` by matching).  fan_lane_active /
#     fan_lane_inactive / fan8_active pin its meaning: active iff k < n.
#
# Past-the-end convention: reads answer the caller's zero/empty -- the
# hist_read / cs_get_row default convention (sweep_nth reads 0.0, str_nth
# reads "").  Out-of-range reads are UNCALLABLE through `swept_param`,
# whose witness cannot be fabricated for k >= len (the checked_read
# convention).
import Base
import ./router.bend as R

# --------------------------------------------------------------------------
# the table: word k of the decoded sweep section
# --------------------------------------------------------------------------

# the table's length -- the bounds witness of the routing laws
def sweep_len(t: List<&2, F32>) -> Nat:
  match t:
    case Nil{}:
      0n
    case h <> t:
      1n+sweep_len(t)

# sim k's parameter: the k-th word of the table.  This is the spec of the
# real `Array.get(U32, sww, k)` in build_and_run.  Past the end: 0.0 (the
# default-read convention; route through swept_param to stay in bounds).
def sweep_nth(t: List<&2, F32>, k: Nat) -> F32:
  match t k:
    case Nil{} _:
      0.0
    case h <> t 0n:
      h
    case h <> t 1n+p:
      sweep_nth(t, p)

# the reference read, built the offset way: drop k rows, take the head.
# An INDEPENDENT implementation of the same read -- sweep_nth_route pins
# the agreement, which is what rules out an off-by-one or stride error in
# either one.
def sweep_drop(t: List<&2, F32>, k: Nat) -> List<&2, F32>:
  match t k:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      h <> t
    case h <> t 1n+p:
      sweep_drop(t, p)

def sweep_head_or(t: List<&2, F32>, +d: F32) -> F32:
  match t:
    case Nil{}:
      d
    case h <> t:
      h

def sweep_word(t: List<&2, F32>, k: Nat) -> F32:
  sweep_head_or(sweep_drop(t, k), 0.0)

# sim k's parameter, callable ONLY when k is inside the table: the witness
# cannot be fabricated for k >= sweep_len(t) (the checked_read convention;
# the negative controls try and fail).
def swept_param(t: List<&2, F32>, k: Nat, -w: R.lt_ok(k, sweep_len(t))) -> F32:
  sweep_nth(t, k)

# --------------------------------------------------------------------------
# the fan: one lane, then the fixed 8-wide fan
# --------------------------------------------------------------------------

# the single-lane gate: lane k runs f(k) iff k < n, else contributes "".
# The spec of `point(k, in, active)` with `active = k < n_sweep`.  The
# recursion shrinks n while REMEMBERING the original k (k0) -- f is
# applied to the lane index the CALLER asked about, never to a shrunken
# one.  f is used at most once per call (affine; functions are not Data).
def fan_lane_go(n: Nat, k: Nat, k0: Nat, f: Nat -> String) -> String:
  match n k:
    case 0n _:
      ""
    case 1n+m 0n:
      f(k0)
    case 1n+m 1n+p:
      fan_lane_go(m, p, k0, f)

def fan_lane(n: Nat, +k: Nat, f: Nat -> String) -> String:
  fan_lane_go(n, k, k, f)

# the k-th entry of a String list, "" past the end (the default-read
# convention; this is runs_nth for the fan's run table)
def str_nth(xs: List<&2, String>, k: Nat) -> String:
  match xs k:
    case Nil{} _:
      ""
    case h <> t 0n:
      h
    case h <> t 1n+p:
      str_nth(t, p)

# the activity gate for one lane: the lane's run iff a > 0, else ""
def gate(a: Nat, +r: String) -> String:
  match a:
    case 0n:
      ""
    case 1n+d:
      r

# the active count and the run table, one lane later
def a_tail(a: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+d:
      d

def str_tail(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

# the w-wide fan: lane i's cell is its run iff i < a, else ""; a short run
# table reads "" (the default-read convention), so the fan is ALWAYS w
# wide -- exactly the real sweep8's fixed 8 lanes.  ONE match, on the
# width: Bend's multi-scrutinee match does not reduce unless every
# scrutinee is a constructor, so the spec keeps each match single-scrutinee
# and reads activity/runs through the total helpers above.  a <= w is the
# intended shape (n_sweep <= 8); a > w silently drops lanes, and the
# gather/nth laws DEMAND the width witness exactly so that shape cannot
# pass.
def fan_go(w: Nat, +a: Nat, +runs: List<&2, String>) -> List<&2, String>:
  match w:
    case 0n:
      Nil{}
    case 1n+s:
      gate(a, str_nth(runs, 0n)) <> fan_go(s, a_tail(a), str_tail(runs))

# the sweep8 mirror: a FIXED 8-WIDE fan, lane k active iff k < n
def fan8(+n: Nat, +runs: List<&2, String>) -> List<&2, String>:
  fan_go(8n, n, runs)

# --------------------------------------------------------------------------
# the reads and the gather
# --------------------------------------------------------------------------

# the lane-ordered concatenation: the spec of the real `x ++ y` chain in
# sweep8/two_str/four_str
def gather(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      h ++ gather(t)

# the SEQUENTIAL reference: the plain concatenation of the first n runs.
# fan_gather_order pins gather(fan8(n, runs)) == seq_gather(n, runs) --
# the parallel fan IS the sequential computation, in lane order.
def seq_gather(+n: Nat, +runs: List<&2, String>) -> String:
  match n:
    case 0n:
      ""
    case 1n+s:
      str_nth(runs, 0n) ++ seq_gather(s, str_tail(runs))

# --------------------------------------------------------------------------
# the sweep validator and the contract bundle (Group 4, the composition)
# --------------------------------------------------------------------------

# THE SWEEP VALIDATOR: the conjunction of the two silent-failure gates.
#   (a) the WIDTH BOUND: the table fits the fixed 8-wide fan.  This is
#       fan8_exact's le_ok(n, 8) witness promoted to a VALIDATOR conjunct:
#       an n_sweep > 8 sweep is a REJECTED config, not a silently
#       truncated run (the drop this layer polices).
#   (b) the SHARED CONFIG's R.ok: every sim of the sweep runs the same
#       base config -- only the swept parameter varies -- so one ok()
#       call covers the whole Monte-Carlo batch.
def sweep_ok(+t: List<&2, F32>, +c: R.Config) -> Bool:
  Bool.and(Nat.is_le(sweep_len(t), 8n), R.ok(c))

# the routing contract's conclusion BUNDLE, as one Bool expression: the
# third conjunct of the sweep capstone (sweep_contract in LAWS_sweep.bend)
# is this bundle equal to True -- Laws.routing_contract's conclusion
# (PROOF_router.bend) at the shared config, spelled here so the capstone
# reads as one claim.  The bridge def routing_contract_at in
# PROOF_router.bend discharges it (filled laws do not re-export across
# module imports; plain defs do).
def routing_bundle(+c: R.Config, +ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>,
                   +t: Nat, +i: Nat) -> Bool:
  Bool.and(Nat.is_le(R.l_i1(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                     R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                               R.proj_src(R.nth_proj(ps, i))))),
           Bool.and(Nat.is_le(Nat.sub(R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                                             R.proj_src(R.nth_proj(ps, i)))),
                                      R.cfg_horizon(c)),
                              R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i))),
                    Nat.is_le(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                              R.l_i1(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)))))

# --------------------------------------------------------------------------
# the 2-LEVEL table: one ROW of parameters per sim (the multi-param sweep)
# --------------------------------------------------------------------------

# the row count -- the bounds witness of the row-routing laws
def rows_len(rows: List<&2, List<&2, F32>>) -> Nat:
  match rows:
    case Nil{}:
      0n
    case h <> t:
      1n+rows_len(t)

# sim i's parameter row: row i of the table; missing rows read as the
# empty row (the cs_row convention, coupling.bend)
def sweep_row(rows: List<&2, List<&2, F32>>, i: Nat) -> List<&2, F32>:
  match rows i:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      h
    case h <> t 1n+p:
      sweep_row(t, p)

# sim i's field j: element j of sim i's row; past-the-end reads 0.0 (the
# sweep_nth default-read convention)
def sweep_field(rows: List<&2, List<&2, F32>>, i: Nat, j: Nat) -> F32:
  sweep_nth(sweep_row(rows, i), j)

# the reference row read, built the offset way: drop i rows, take the head
# (the sweep_drop / sweep_word pattern at the row level).  An INDEPENDENT
# implementation of the same read -- sweep_row_nth pins the agreement.
def rows_drop(rows: List<&2, List<&2, F32>>, k: Nat) -> List<&2, List<&2, F32>>:
  match rows k:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      h <> t
    case h <> t 1n+p:
      rows_drop(t, p)

def rows_head_or(rows: List<&2, List<&2, F32>>, +d: List<&2, F32>) -> List<&2, F32>:
  match rows:
    case Nil{}:
      d
    case h <> t:
      h

def sweep_row_ref(rows: List<&2, List<&2, F32>>, i: Nat) -> List<&2, F32>:
  rows_head_or(rows_drop(rows, i), Nil{})

# --------------------------------------------------------------------------
# the row-major WIRE: the packed flat table and its two reads
# --------------------------------------------------------------------------

# the row-major address: row i, field j of a w-wide packed flat table
# lives at flat index i*w + j

def flat_addr(i: Nat, w: Nat, j: Nat) -> Nat:
  Nat.add(Nat.mul(i, w), j)

# the wire read, the CLOSED-FORM way: one address, one read (the spec of
# the packed sweep section's word at base + i*w + j)
def flat_at(flat: List<&2, F32>, i: Nat, w: Nat, j: Nat) -> F32:
  sweep_nth(flat, flat_addr(i, w, j))

# the wire read, the STRUCTURAL way: skip i whole rows of w, then read
# field j.  The recursion shrinks the row counter i (the drop happens
# after it, so the termination checker sees i shrink first).
def flat_read_go(+w: Nat, i: Nat, flat: List<&2, F32>, j: Nat) -> F32:
  match i:
    case 0n:
      sweep_nth(flat, j)
    case 1n+p:
      flat_read_go(w, p, sweep_drop(flat, w), j)

def flat_read(flat: List<&2, F32>, i: Nat, w: Nat, j: Nat) -> F32:
  flat_read_go(w, i, flat, j)

# --------------------------------------------------------------------------
# the COLUMN->ROW assembly (the TVB sweep API's orientation)
# --------------------------------------------------------------------------

# param j's COLUMN: its values across sims; missing columns read as the
# empty column (the cs_row shape again -- a column is a list of sims too)
def col_nth(cols: List<&2, List<&2, F32>>, j: Nat) -> List<&2, F32>:
  sweep_row(cols, j)

# sim i's row, ASSEMBLED from the columns: element i of column 0, element
# i of column 1, .. -- the per-sim row the named-key API builds
def col_row_go(cols: List<&2, List<&2, F32>>, +i: Nat) -> List<&2, F32>:
  match cols:
    case Nil{}:
      Nil{}
    case c <> rest:
      sweep_nth(c, i) <> col_row_go(rest, i)

def col_row(cols: List<&2, List<&2, F32>>, i: Nat) -> List<&2, F32>:
  col_row_go(cols, i)

# --------------------------------------------------------------------------
# the ASSEMBLED ROW TABLE (the JSON column ingress's table): one assembled
# row per sim, sims 0 .. (first column's length) - 1 -- the table the JSON
# sweep ingress validates (sweep_rows_ok) and the capstone routes
# --------------------------------------------------------------------------

# the column table's sim count: the first column's length (a consistent
# table -- every column the same length, the ingress's sw_consistent --
# has exactly this many sims; missing columns read empty, so 0 columns
# give 0 sims)
def cols_ns(cols: List<&2, List<&2, F32>>) -> Nat:
  sweep_len(col_nth(cols, 0n))

# the builder's spine: k counts the rows DOWN while i counts the sims UP
# (the counted-loop convention: the shrinking argument leads)
def cols_rows_go(+cols: List<&2, List<&2, F32>>, k: Nat, +i: Nat) -> List<&2, List<&2, F32>>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      col_row(cols, i) <> cols_rows_go(cols, p, 1n+i)

# the assembled row table: row i IS col_row(cols, i) for i < cols_ns(cols)
def cols_rows(+cols: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  cols_rows_go(cols, cols_ns(cols), 0n)

# --------------------------------------------------------------------------
# the ROW-TABLE validator (sweep_ok's multi-param generalization)
# --------------------------------------------------------------------------

# the ROW-SHAPE check: EVERY row has exactly wp fields -- one Bool, so the
# every-row quantifier is a fold (the nats_lt_all pattern)
def rows_shape_ok(rows: List<&2, List<&2, F32>>, +wp: Nat) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case r <> t:
      Bool.and(Nat.is_eq(sweep_len(r), wp), rows_shape_ok(t, wp))

# THE ROW-TABLE VALIDATOR: the sweep_ok generalization for the multi-param
# sweep.  (a) the WIDTH bound at the CURRENT engine's 8 lanes (the flat
# sweep_ok's conjunct, unchanged); (b) the ROW SHAPE: every row carries
# exactly wp parameters -- a ragged table is a REJECTED config, not a
# silently mis-routed sim (a short row's missing fields read the 0.0
# default and the sim runs with garbage parameters); (c) the SHARED
# CONFIG's R.ok, unchanged.
def sweep_rows_ok(+rows: List<&2, List<&2, F32>>, +wp: Nat, +c: R.Config) -> Bool:
  Bool.and(Nat.is_le(rows_len(rows), 8n),
           Bool.and(rows_shape_ok(rows, wp), R.ok(c)))
