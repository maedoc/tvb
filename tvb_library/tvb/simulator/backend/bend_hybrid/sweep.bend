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

# --------------------------------------------------------------------------
# the CONNECTOME sweep (SWEEP_LAWS_DESIGN.md, priority P2): a per-sim CSR
# PAYLOAD with the SHARED shape.  Every sim of the sweep runs the SAME
# connectome SHAPE -- fixed node count, fixed edge layout, one shared
# (indptr, indices) pair -- and varies only the per-edge VALUES: the
# weights (one F32 per edge) and the delays (one Nat per edge).  NO model
# sweeps: the structural object swept here is the CSR payload only.
#
# REPRESENTATION (decided): the table is a `List<&2, CsrPay>` -- ONE
# payload RECORD per sim (weights and delays together), not parallel
# weight/delay lists.  A record keeps the (weights, delays) pair aligned
# per sim by construction (the same no-desynchronization argument as
# edge_lines_from's flat (src, delay) read), and the row routing is ONE
# law over the record instead of two over parallel lists.  The shared
# shape (indptr, indices) lives OUTSIDE the table: it is one argument of
# the validator and of the row->CSR builder, shared by every sim.
#
# A row's CSR -- the object the router's csr_ok and csr_row_* machinery
# consume -- is the shared (indptr, indices) paired with the row's
# delays.  The weights ride alongside (the router's Csr has no weight
# field; the engine folds the weight separately in its gather).
type CsrPay is Data:
  CsrPay{weights: List<&2, F32>, delays: List<&2, Nat>}

def pay_weights(+p: CsrPay) -> List<&2, F32>:
  match p:
    case CsrPay{weights, delays}:
      weights

def pay_delays(+p: CsrPay) -> List<&2, Nat>:
  match p:
    case CsrPay{weights, delays}:
      delays

# sim i's CSR: the SHARED indptr/indices with sim i's delays -- the
# per-sim object the router's R.csr_ok validates and csr_row_* reads
def pay_csr(+indptr: List<&2, Nat>, +ixs: List<&2, Nat>, +p: CsrPay) -> R.Csr:
  R.Csr{indptr, ixs, pay_delays(p)}

# the payload table's length -- the bounds witness of the routing laws
# (the rows_len pattern at the payload level)
def pays_len(pays: List<&2, CsrPay>) -> Nat:
  match pays:
    case Nil{}:
      0n
    case h <> t:
      1n+pays_len(t)

# sim i's payload: the i-th payload record; missing rows read as the
# empty payload (the sweep_row / cs_row default convention)
def pay_nth(pays: List<&2, CsrPay>, i: Nat) -> CsrPay:
  match pays i:
    case Nil{} _:
      CsrPay{Nil{}, Nil{}}
    case h <> t 0n:
      h
    case h <> t 1n+p:
      pay_nth(t, p)

# the reference payload read, built the offset way: drop i rows, take the
# head (the rows_drop / rows_head_or pattern).  An INDEPENDENT
# implementation of the same read -- sweep_csr_route pins the agreement,
# which is what rules out an off-by-one in the structural payload read.
def pays_drop(pays: List<&2, CsrPay>, k: Nat) -> List<&2, CsrPay>:
  match pays k:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      h <> t
    case h <> t 1n+p:
      pays_drop(t, p)

def pays_head_or(pays: List<&2, CsrPay>, +d: CsrPay) -> CsrPay:
  match pays:
    case Nil{}:
      d
    case h <> t:
      h

def pay_ref(pays: List<&2, CsrPay>, i: Nat) -> CsrPay:
  pays_head_or(pays_drop(pays, i), CsrPay{Nil{}, Nil{}})

# ONE row's SHAPE check: the payload is the same length as the shared
# edge layout -- as many weights as the shared indices declare AND as
# many delays (the fixed edge count of the identical-shape sweep)
def pay_shape_ok(+p: CsrPay, +n: Nat) -> Bool:
  Bool.and(Nat.is_eq(sweep_len(pay_weights(p)), n),
           Nat.is_eq(R.nats_len(pay_delays(p)), n))

# the SHARED-SHAPE fold: EVERY row's payload matches the shared edge
# count -- one Bool, the rows_shape_ok fold at the payload level.  n is
# the shared edge count, nats_len(indices) at the call site.
def cs_shape_ok(+pays: List<&2, CsrPay>, +n: Nat) -> Bool:
  match pays:
    case Nil{}:
      True{}
    case p <> t:
      Bool.and(pay_shape_ok(p, n), cs_shape_ok(t, n))

# the PER-ROW csr_ok fold: EVERY row's CSR -- shared indptr/indices with
# the row's delays -- passes the router's R.csr_ok (nsrc = the shared
# node count, horizon = the shared config's horizon).  The shared arrays'
# own invariants (first-zero, sorted, last == |indices|, indices in
# range) are re-checked per row by R.csr_ok -- redundant across rows but
# honest: the fold IS the per-sim validation the engine would run.
def cs_rows_csr_ok(+nsrc: Nat, +horizon: Nat, +indptr: List<&2, Nat>,
                   +ixs: List<&2, Nat>, +pays: List<&2, CsrPay>) -> Bool:
  match pays:
    case Nil{}:
      True{}
    case p <> t:
      Bool.and(R.csr_ok(nsrc, horizon, pay_csr(indptr, ixs, p)),
               cs_rows_csr_ok(nsrc, horizon, indptr, ixs, t))

# THE CONNECTOME-SWEEP VALIDATOR: sweep_ok's structural-payload
# generalization, four conjuncts:
#   (a) the WIDTH bound: the payload table fits the fixed 8-wide fan
#       (the same silent-drop gate as the scalar sweep);
#   (b) the SHARED SHAPE: every row's payload is as long as the shared
#       edge layout -- a short row would silently default its missing
#       weights/delays (the ragged-row mode, at the CSR level);
#   (c) the PER-ROW csr_ok: every row's CSR (shared shape + row delays)
#       passes the router's connectome validation -- an out-of-bounds
#       source index or horizon-breaking delay is a REJECTED config;
#   (d) the SHARED CONFIG's R.ok, unchanged (one ok() call covers the
#       whole batch -- only the payload varies per sim).
# nsrc and horizon come from the shared config: the node count IS the
# shared config's lane count, the delay bound IS its horizon.
def sweep_csr_ok(+indptr: List<&2, Nat>, +ixs: List<&2, Nat>,
                 +pays: List<&2, CsrPay>, +c: R.Config) -> Bool:
  Bool.and(Nat.is_le(pays_len(pays), 8n),
  Bool.and(cs_shape_ok(pays, R.nats_len(ixs)),
  Bool.and(cs_rows_csr_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
                          indptr, ixs, pays),
           R.ok(c))))

# --------------------------------------------------------------------------
# P3b -- the STOCHASTIC SEED column (SWEEP_LAWS_DESIGN.md, priority P3):
# sim i's noise stream is seeded by the seed column's element i.
#
# The column is a `List<&2, Nat>` -- the sweep_nth machinery over a Nat
# column (seed_nth the recursive read, seed_ref the drop+head reference;
# seed_route pins the agreement, which is what rules out an off-by-one in
# the seed read).
#
# DESIGN CHOICE (the distinctness story, decided): the by-construction
# assignment.  The fan's seeds are seed_row(base, n) = [base+0 .. base+n-1]
# -- the seed column the engine BUILDS, not one it is handed -- so two
# distinct sims never share a seed is ADD-INJECTIVITY (seed_distinct:
# is_ne(base+i, base+j) for i < j), a small arithmetic law, with no
# column hypothesis needed.  A general (e.g. JSON-supplied) seed column is
# still covered: sweep_seed_ok carries a DISTINCTNESS fold (seeds_unique,
# the router's writes_unique/ok_no_clash pattern) that rejects a duplicate
# pair at load time (bad/bad_seed.bend), and seeds_distinct_nth pins the
# per-index form.

# sim i's seed: element i of the seed column.  Past the end: 0n (the
# sweep_nth default-read convention; route through the validator's width
# bound to stay in bounds).
def seed_nth(xs: List<&2, Nat>, k: Nat) -> Nat:
  match xs k:
    case Nil{} _:
      0n
    case h <> t 0n:
      h
    case h <> t 1n+p:
      seed_nth(t, p)

# the reference seed read, built the offset way: drop k elements, take the
# head.  An INDEPENDENT implementation of the same read -- seed_route pins
# the agreement (the sweep_nth_route pattern over a Nat column).
def seeds_drop(xs: List<&2, Nat>, k: Nat) -> List<&2, Nat>:
  match xs k:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      h <> t
    case h <> t 1n+p:
      seeds_drop(t, p)

def seeds_head_or(xs: List<&2, Nat>, +d: Nat) -> Nat:
  match xs:
    case Nil{}:
      d
    case h <> t:
      h

def seed_ref(xs: List<&2, Nat>, k: Nat) -> Nat:
  seeds_head_or(seeds_drop(xs, k), 0n)

# the BY-CONSTRUCTION seed assignment: n seeds, seed i IS base + i -- the
# counted-loop builder (the cols_rows_go convention: the shrinking counter
# k leads, the sim index j rides).
def seed_row_go(+base: Nat, k: Nat, +j: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Nat.add(base, j) <> seed_row_go(base, p, 1n+j)

def seed_row(+base: Nat, +n: Nat) -> List<&2, Nat>:
  seed_row_go(base, n, 0n)

# the distinctness machinery for a GENERAL seed column (the router's
# writes_unique / ok_no_clash pattern over Nats): s clashes with no later
# element, and the pairwise fold.
def no_seed_clash(+s: Nat, ts: List<&2, Nat>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case h <> +t:
      Bool.and(Nat.is_ne(s, h), no_seed_clash(s, t))

def seeds_unique(seeds: List<&2, Nat>) -> Bool:
  match seeds:
    case Nil{}:
      True{}
    case h <> +t:
      Bool.and(no_seed_clash(h, t), seeds_unique(t))

# THE SEED VALIDATOR: (a) the WIDTH bound -- the seed column fits the
# fixed 8-wide fan (one seed per sim, the same silent-drop gate as the
# parameter table); (b) the DISTINCTNESS fold -- a duplicate seed pair
# would alias two sims' noise streams onto one stream (the silent-
# correlation mode); (c) the SHARED CONFIG's R.ok, unchanged.
def sweep_seed_ok(+seeds: List<&2, Nat>, +c: R.Config) -> Bool:
  Bool.and(Nat.is_le(R.nats_len(seeds), 8n),
           Bool.and(seeds_unique(seeds), R.ok(c)))

# --------------------------------------------------------------------------
# P5 -- the OUTPUT UN-ROUTING (SWEEP_LAWS_DESIGN.md, gap 9): which slice of
# the sweep's output belongs to which subnet x sim -- the reverse routing,
# the demos' per-subnet extraction (simulate_hybrid_getting_started.py:
# "the per-subnetwork time series are CONCATENATED in the order they appear
# in subnets"; a sweep adds the outer per-sim dimension).
#
# REPRESENTATION (the cs shape, one level up): one sim's output BLOCK is a
# `List<&2, List<&2, F32>>` -- one SERIES (List<&2, F32>) per subnet, in
# subnet order; a sweep's output is a `List<&2, List<&2, List<&2, F32>>>`
# -- one block per sim, in lane order.  The reads reuse the coupling
# state's 2-level read pattern out of the box: out_block is the cs_row
# read at the block level, and the series WITHIN a block is read by
# sweep_row / sweep_row_ref (the proved row reads -- a block IS a row
# table whose rows are series).
#
# THE OUTPUT IS THE FAN'S PRODUCT: out_fan is the output plane's fan --
# the same fixed-8-wide lane/gate structure as fan8 (lane k active iff
# k < n, the SAME activity decider), with each active lane contributing
# ITS run's output block.  Inactive lanes contribute NOTHING (not an
# empty block): the gathered output has exactly n_sims blocks -- the
# string fan's "" cells exist because gather needs a String per lane; at
# the block plane the per-sim blocks are the concatenation, and the empty
# block would be a phantom sim's output.
# --------------------------------------------------------------------------

# the sweep output's block count -- the outer bounds witness

def outs_len(outs: List<&2, List<&2, List<&2, F32>>>) -> Nat:
  match outs:
    case Nil{}:
      0n
    case h <> t:
      1n+outs_len(t)

# sim i's output block: block i of the sweep's output; missing blocks read
# as the empty block (the cs_row default convention)
def out_block(outs: List<&2, List<&2, List<&2, F32>>>,
              i: Nat) -> List<&2, List<&2, F32>>:
  match outs i:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      h
    case h <> t 1n+p:
      out_block(t, p)

# the reference block read, built the offset way: drop i blocks, take the
# head (the rows_drop / rows_head_or pattern).  An INDEPENDENT
# implementation of the same read -- out_route pins the agreement, which
# is what rules out an off-by-one in the un-routing.
def outs_drop(outs: List<&2, List<&2, List<&2, F32>>>,
              k: Nat) -> List<&2, List<&2, List<&2, F32>>>:
  match outs k:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      h <> t
    case h <> t 1n+p:
      outs_drop(t, p)

def outs_head_or(outs: List<&2, List<&2, List<&2, F32>>>,
                 +d: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match outs:
    case Nil{}:
      d
    case h <> t:
      h

def out_block_ref(outs: List<&2, List<&2, List<&2, F32>>>,
                  i: Nat) -> List<&2, List<&2, F32>>:
  outs_head_or(outs_drop(outs, i), Nil{})

# subnet s's series of sim i's block: the cs_get pattern -- read the
# block, then the series within it (sweep_row, the proved row read; a
# block's rows ARE series).  Past either end: the empty series.
def out_slice(outs: List<&2, List<&2, List<&2, F32>>>, i: Nat,
             s: Nat) -> List<&2, F32>:
  sweep_row(out_block(outs, i), s)

def out_slice_ref(outs: List<&2, List<&2, List<&2, F32>>>, i: Nat,
                  s: Nat) -> List<&2, F32>:
  sweep_row_ref(out_block_ref(outs, i), s)

# the block table's tail (the str_tail pattern at the block level)
def outs_tail(outs: List<&2, List<&2, List<&2, F32>>>)
  -> List<&2, List<&2, List<&2, F32>>>:
  match outs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

# lane k's contribution: its block consed onto the rest iff k < a, else
# just the rest (inactive lanes contribute NOTHING -- the empty block
# would be a phantom sim's output).  The total decider keeps out_fan_go
# single-scrutinee (the fan_go convention: the laws' go-lemmas must see
# through the fan's recursion).
def lane_cons(a: Nat, +r: List<&2, List<&2, F32>>,
              +rest: List<&2, List<&2, List<&2, F32>>>)
  -> List<&2, List<&2, List<&2, F32>>>:
  match a:
    case 0n:
      rest
    case 1n+d:
      r <> rest

# the output plane's fan: the fixed 8-wide fan over per-sim output blocks
# -- lane k's block iff k < n, else nothing.
def out_fan_go(w: Nat, +a: Nat,
               +blocks: List<&2, List<&2, List<&2, F32>>>)
  -> List<&2, List<&2, List<&2, F32>>>:
  match w:
    case 0n:
      Nil{}
    case 1n+s:
      lane_cons(a, out_block(blocks, 0n),
                out_fan_go(s, a_tail(a), outs_tail(blocks)))

def out_fan(+n: Nat, +blocks: List<&2, List<&2, List<&2, F32>>>)
  -> List<&2, List<&2, List<&2, F32>>>:
  out_fan_go(8n, n, blocks)

# the per-sim block BUILDER: one series per subnet, subnets in lane order
# -- the demos' per-subnet extraction reversed (the engine writes one
# series per subnet of the shared config).  A short series list yields
# EMPTY series (the sweep_row default), never a short block: the block's
# shape is the config's subnet count BY CONSTRUCTION -- out_block_len pins
# it.
def block_go(k: Nat, +series: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      sweep_row(series, 0n) <> block_go(p, rows_drop(series, 1n))

def block_of(+n: Nat, +series: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  block_go(n, series)

# --------------------------------------------------------------------------
# P6 -- the GRID (SWEEP_LAWS_DESIGN.md, gap 8): the row = grid-point
# construction.  A grid is a CROSS PRODUCT of independent per-dimension
# RANGES, enumerated row-major over the per-dimension lengths: dimension 0
# is the SLOWEST-varying index and the last dimension varies fastest.
# Each grid point is a SWEEP ROW (one value per dimension), so a grid
# routes through the existing sweep_nth / fan machinery unchanged.
#
# REPRESENTATION: the grid is `List<&2, List<&2, F32>>` -- dimension j's
# range is element j -- the SAME COLUMNS shape the JSON sweep ingress
# decodes (sweep_names / sweep_cols, values integer-scaled): a grid over
# the decoded columns enumerates the cross product of the supplied
# ranges.  grid_len is the PRODUCT of the per-dimension lengths (the
# grid's sim count); grid_ok = every dimension NONEMPTY (an empty dim
# would sweep nothing) /\ the product fits the fixed 8-wide fan (the
# sweep_ok width conjunct) /\ the shared config's R.ok.  The bounds guard
# grid_point is the swept_param analog: an out-of-range index's witness
# cannot be fabricated.
#
# THE MIXED-RADIX DECOMPOSITION (the flat_nth brick at grid level): the
# i-th grid point's coordinate in dimension j is the mixed-radix digit of
# i -- i = d_0*P_0 + d_1*P_1 + ... with P_j = grid_len(dims after j).
# grid_dim_len / grid_len give the radices; split is the digit extractor
# (Base Nat.divmod's countdown machine, re-worked as a Data record whose
# recursion the proofs can match); grid_row walks the dimensions splitting
# the current index by the TAIL product (row-major: the first dim's digit
# is the biggest stride) and reads each dimension's value at its digit.
# The walk is TOTAL: a past-the-end index keeps splitting (the digit then
# reads a default 0.0), so reads stay total while the GUARD rejects.
# --------------------------------------------------------------------------

# the mixed-radix split: for B > 0 (B = 0 is total junk), split(B, i) =
# (i div B, i mod B): the digit and the remainder of one radix.
type Split is Data:
  Split{d: Nat, r: Nat}

def split_d(+s: Split) -> Nat:
  match s:
    case Split{d, r}:
      d

def split_r(+s: Split) -> Nat:
  match s:
    case Split{d, r}:
      r

# the countdown machine (the Base Nat.divmod.go clock, record-shaped):
# (n, m, d, r) -- n the unconsumed index, m the co-countdown from B-1,
# d the quotient, r the remainder.  Halt when n = 0: the answer (d, r).
def split_go(n: Nat, m: Nat, d: Nat, r: Nat) -> Split:
  match n m:
    case 0n _:
      Split{d, r}
    case 1n+np 0n:
      split_go(np, r, 1n+d, 0n)
    case 1n+np 1n+mp:
      split_go(np, mp, d, 1n+r)

def split(+B: Nat, i: Nat) -> Split:
  match B:
    case 0n:
      Split{0n, i}
    case 1n+bp:
      split_go(i, bp, 0n, 0n)

# dimension j's RANGE: element j of the grid (a column of values); past
# the end: the empty range (the sweep_row default-read convention)
def grid_dim(gs: List<&2, List<&2, F32>>, j: Nat) -> List<&2, F32>:
  sweep_row(gs, j)

# dimension j's LENGTH -- the j-th radix of the mixed-radix decomposition
def grid_dim_len(gs: List<&2, List<&2, F32>>, j: Nat) -> Nat:
  sweep_len(grid_dim(gs, j))

# the product of the per-dimension lengths: the grid's sim count -- the
# mixed-radix decoding's stride base (Nat.mul's recursion on the FIRST
# argument is the shape the length law recurses through)
def grid_len(gs: List<&2, List<&2, F32>>) -> Nat:
  match gs:
    case Nil{}:
      1n
    case r <> t:
      Nat.mul(sweep_len(r), grid_len(t))

# the every-dimension-nonempty fold: an empty range is a REJECTED grid
# (it would sweep nothing; split needs B > 0 to be a radix)
def grid_nonempty(gs: List<&2, List<&2, F32>>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case r <> t:
      Bool.and(Nat.is_ne(sweep_len(r), 0n), grid_nonempty(t))

# THE GRID VALIDATOR -- the sweep_ok generalization:
#   (a) EVERY DIMENSION NONEMPTY (the fold above);
#   (b) the WIDTH bound: the product fits the fixed 8-wide fan (the
#       sweep_ok conjunct; a grid whose total exceeds 8 would silently
#       drop points, the n_sweep > 8 failure mode at the grid level);
#   (c) the SHARED CONFIG's R.ok (one call covers the whole grid batch).
# The row SHAPE needs no conjunct: every grid point is a row of exactly
# one value per dimension BY CONSTRUCTION (grid_row_shape pins it).
def grid_ok(+gs: List<&2, List<&2, F32>>, +c: R.Config) -> Bool:
  Bool.and(grid_nonempty(gs), Bool.and(Nat.is_le(grid_len(gs), 8n), R.ok(c)))

# the COORDINATE WALK: the list of the i-th grid point's coordinates,
# one mixed-radix digit per dimension, in dimension order (the row-major
# order: the first dim's digit is the biggest stride -- the tail product)
def grid_coords_go(gs: List<&2, List<&2, F32>>, +i: Nat) -> List<&2, Nat>:
  match gs:
    case Nil{}:
      Nil{}
    case r <> +rest:
      split_d(split(grid_len(rest), i)) <> grid_coords_go(rest,
                                                          split_r(split(grid_len(rest), i)))

def grid_coords(gs: List<&2, List<&2, F32>>, i: Nat) -> List<&2, Nat>:
  grid_coords_go(gs, i)

# coordinate j of grid point i: the DIRECT digit extraction -- the same
# walk as the coords list, one digit without building the rest (the
# index remainder rides the split; grid_coords_digit pins that this IS
# the mixed-radix digit the list carries)
def grid_digit_go(gs: List<&2, List<&2, F32>>, +i: Nat, j: Nat) -> Nat:
  match gs j:
    case Nil{} _:
      0n
    case r <> +rest 0n:
      split_d(split(grid_len(rest), i))
    case r <> +rest 1n+p:
      grid_digit_go(rest, split_r(split(grid_len(rest), i)), p)

def grid_digit(gs: List<&2, List<&2, F32>>, i: Nat, j: Nat) -> Nat:
  grid_digit_go(gs, i, j)

# the i-th grid point AS A SWEEP ROW: one value per dimension, dimension
# j's value read at coordinate j of grid point i -- the ROW the sweep row
# machinery routes unchanged (grid rows ARE sweep rows).  Total: a
# past-the-end index reads whatever digit its continued split reaches
# (the default-read convention; route through grid_point to stay in
# bounds -- past-the-end points are REJECTED, not wrapped).
def grid_row_go(gs: List<&2, List<&2, F32>>, +i: Nat) -> List<&2, F32>:
  match gs:
    case Nil{}:
      Nil{}
    case r <> +rest:
      sweep_nth(r, split_d(split(grid_len(rest), i)))
        <> grid_row_go(rest, split_r(split(grid_len(rest), i)))

def grid_row(gs: List<&2, List<&2, F32>>, i: Nat) -> List<&2, F32>:
  grid_row_go(gs, i)

# the grid point read, callable ONLY for an in-bounds index -- the
# swept_param convention: the witness lt_ok(i, grid_len(gs)) cannot be
# fabricated for i >= total, which is the past-the-end REJECTION (an
# out-of-range grid point is not a grid point).
def grid_point(gs: List<&2, List<&2, F32>>, i: Nat,
               -w: R.lt_ok(i, grid_len(gs))) -> List<&2, F32>:
  grid_row(gs, i)

# the DECODING of a coordinate vector back to an index: sum of
# digit_j * stride_j (stride_j = grid_len of the dims after j) -- the
# "mixed-radix injectivity" witness direction.  grid_index_inst pins the
# round trip on literal grids (i < total: the digits decode back to i).
def grid_index_go(gs: List<&2, List<&2, F32>>,
                  cs: List<&2, Nat>) -> Nat:
  match gs cs:
    case Nil{} Nil{}:
      0n
    case Nil{} c0 <> t:
      0n
    case r <> rest Nil{}:
      0n
    case r <> +rest c0 <> t:
      Nat.add(Nat.mul(c0, grid_len(rest)), grid_index_go(rest, t))

def grid_index(gs: List<&2, List<&2, F32>>,
               cs: List<&2, Nat>) -> Nat:
  grid_index_go(gs, cs)
