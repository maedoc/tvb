# Sweep laws design — proving the parameter routing of the Monte-Carlo sweep

> **New here?** Start with [README.md](README.md) — the guided tour (goals, data structures, the high-level laws). This file is a design note.
>
> **Status: implemented** — LAWS_sweep.bend / PROOF_sweep.bend (37 laws, gates green). All five groups landed, incl. the JSON sweep ingress (columns schema) and the name->slot field-map.

*Design note, 2026-10-05. Scope: what laws would prove that the sweep's
parameter rows route to the right sims, and what the proofs look like.
Target: the JSON-supplied per-sim parameter sets (the current prototype
uses a packed-word job file; the law layer is format-agnostic — the same
table spec serves both ingresses).*

## What the sweep is today

`montbrio_sweep.bend`: one job file carries `n_sweep` sims; the sweep
section is `n_sweep` 4-byte words (one varying F32 per sim today). The
fan is **fixed 8-wide** (`sweep8`): lane `k` runs `point(k, in, active)`
with `active = k < n_sweep` — inactive lanes cost a match, not a sim —
and `build_and_run(k, ...)` reads **word k** of the decoded sweep table
(`Array.get(U32, sww, k)`). Outputs concatenate in lane order.

The silent-failure mode this exposes: **`n_sweep > 8` drops sims without
any error** (the fan is fixed-width). The laws below make the width
bound a required witness.

## What "correct routing" means — the failure modes

1. **mis-routing**: sim `i` reads the wrong parameter row (off-by-one,
   stride error in the packed table);
2. **coverage**: a row dropped or duplicated (fan split wrong);
3. **gather**: sim `i`'s result lands in another row's output block;
4. **validation**: a malformed row sneaks through to a sim;
5. **nondeterminism**: the parallel execution order changes the result.

## The spec objects (`sweep.bend`, pure — the list is the spec)

- **the table** — `List<&2, F32>` (one varying parameter per sim today)
  or `List<&2, List<&2, F32>>` (the JSON row-set future: one row of
  parameters per sim — the same 2-level shape as coupling.bend's `cs`,
  whose `cs_row`/`cs_get_row` and their proved read/stability laws are
  directly reusable).
- **the fan** — `fan(w, n, f)`: a `w`-wide fan where lane `k` runs
  `f(k)` iff `k < n`, else contributes nothing.
- **the gather** — lane-ordered concatenation.

## The laws (statement sketches + proof strategy)

### Group 1 — the row routing (the user's priority claim)

```
law sweep_row_nth:
  for +rows: List<&2, List<&2, F32>>
  for i: Nat
  for h: R.lt_ok(i, <nrows>)
  {sweep_row(rows, i) == the i-th row : ...}
```
sim `i`'s parameters **are** row `i`. Bricks: `cs_row`-level nth laws
(from the coupling work) + the flat/nested agreement (the packed word at
`base + i*w + j` reads row `i` field `j` — the `slice_nth` pattern with
row-major indexing; the mul-add brick `(1n+i)*w + j = w + (i*w + j)`).

Decode half: `to_words` (bytes → words, 4 bytes LE per word) is the
`packed_edge_*` roundtrip idiom already in `LAWS.bend` — the sweep
table's decode laws are the same family. The Array side is the
implementation (list = spec, `Array.get` = the fence, tape/ring style).

Instance pin: `sweep_row_instance` — a literal 3-sim table routes rows
to sims 0, 1, 2 (the csr_row_good convention).

### Group 2 — the fan coverage

```
law fan_exact:
  for +n: Nat
  for +f: (U32 -> String)
  for hw: R.le_ok(n, 8n)          # the width bound, load-bearing
  {sweep8-style fan output == concat of f(0) .. f(n-1) : String}
```
the active lanes are exactly `0..n−1`, each once — every sim runs, none
twice. Proof: finite unrolling of the 8-wide fan (8 cases) or induction
on a general `fan(n, w)`. The width witness is the point: it rejects the
`n_sweep > 8` silent drop.

Negative control: `bad/bad_sweep_width.bend` — the same claim *without*
the `n ≤ 8` witness must be rejected.

### Group 3 — the gather

```
law fan_gather:
  ...{lane-order concat == sequential concat 0..n-1 : String}
```
the output block of sim `i` lands at output position `i`. Definitional
off the `x ++ y` chain once the fan's shape is pinned — a one-line law
that costs little and pins the order (a future reordering breaks it).

### Group 4 — the composition (the sweep contract)

```
law sweep_contract:
  for +rows, for i, h: R.lt_ok(i, nrows), for +hok: <all rows validated>
  {sim i's params == row i  AND  output block i == sim i's result  AND
   sim i's run satisfies the per-sim routing contract}
```
- per-row validation composes with the per-sim `ok()` — the
  `lanes_nth_valid` pattern (`sweep_valid_nth`: a validated sweep makes
  every row valid).
- the **JSON ingress** variant: total `json_sweep_decode` (the
  `json_ingest` state-machine pattern — garbage decodes to the empty
  sweep), the instance pins, and `json_sweep_contract` quantified over
  all strings (the `json_read_fresh` analog).

### Group 5 — parallelism invariance (the Monte-Carlo claim)

```
law sweep_parallel_eq:
  for +n, +f
  {fan(n, f) == sequential(n, f) : String}
```
the fan's result equals the sequential fold — the "embarrassingly
parallel is correct" claim. In a pure language this is nearly
definitional, but stating it pins that the parallel fan *is* the
sequential computation — the refactor a runtime cannot violate.

## Where it lands

- `sweep.bend` (the spec objects) — imports router/hist/coupling.
- `LAWS_sweep.bend` + `PROOF_sweep.bend` — the claims and proofs.
- `tests/run_sweep.sh` — the third gate (`--verdict` + the width
  negative control + a pinned multi-sim sweep test).
- `bad/bad_sweep_width.bend` — the negative control.

## Open questions

- The JSON schema: per-sim rows (`{"sims": [{"scale": ..}, ..]}`) or
  per-parameter columns (`{"scale": [..], ..}`)? The table spec is
  agnostic; the ingress laws pin whichever we choose.
- Fixed-width 8 vs general `fan(n, w)` with `w` a job field: the laws
  pin whichever exists; a general fan makes the width witness the
  honest claim.

## Effort

~15 laws + proofs. The bricks (`take_nth`, `slice_nth`, the Equal
plumbing, the packed-word roundtrip family, the `cs_row` 2-level read
laws) all exist. The hardest single law is the flat/nested agreement
(row-major indexing); the rest are instantiation or short inductions.

## Refresh 2026-10-05 — what the hybrid demos change

Re-read `tvb_documentation/demos/simulate_hybrid_*.py`. Three findings
that reshape the plan:

1. **The sweep schema question is answered: COLUMNS.** The TVB sweep API
   is named keys to per-parameter value lists —
   `backend.sweep(params={"coupling_scale": [v0, ..]})`. So the JSON
   sweep ingress should be per-parameter columns, and the per-sim row is
   ASSEMBLED from them: row i field j = column j's i-th value. The
   row-assembly law (col_to_row) pins that orientation; the row-major
   flat_nth brick pins the wire layout.
2. **The demos sweep 20 points** — over the 8-wide fan. The
   general-width laws (fan_exact at abstract w, the chunked-split
   coverage law) are not a nicety; the real engine needs them now.
   Also: the demo verifies parallel == sequential bit-exactly as a TEST
   — the engine-side mirror of fan_gather_order; the law is the
   spec-level version of the same property.
3. **Subnets are heterogeneous MODELS, not just heterogeneous dts.**
   getting_started pairs JansenRit (cortex) with ReducedSetFitzHughNagumo
   (thalamus): different state_variables, different cvars, and the
   InterProjection maps NAMED cvars across models (source_cvar='y1' on
   JansenRit, target_cvar='xi' on FHN) — the coupling slot is
   MODEL-RELATIVE, resolved against each model's own state_variables.

## The config-complexity layer (the refreshed plan's new family)

The current Config carries per-lane periods only. A model-aware config
carries, per subnet: (model id, n_svars, the cvar list) — and per
projection: source/target cvar indices into the RESPECTIVE models. The
new law family:

- `proj_src_cvar_bounded` / `proj_tgt_cvar_bounded`: a projection's cvar
  indices are within the source/target subnet's model cvar count — the
  proj_src_bounded analog one level down (model-relative). The validator
  conjunct family (ok inversion, per-index forms) follows the section-6
  pattern.
- the name-resolution law: the cvar NAME resolves against the model's
  state_variables to exactly the index the projection uses (a table
  lookup law — the JSON string resolution pinned).
- and the sweep composes: a sweep's per-sim configs are the base config
  plus the named column values patched into their slots (the field-map
  law), each validated by the model-aware ok.

## Sweep v2 (the generalization being implemented now)

- fan_exact at general width w (the width witness becomes le_ok(n, w);
  fan8_exact stays as the w=8 instance; the existing proof already
  inducts over the general fan_go).
- the multi-param row table: 2-level rows (the cs_row/cs_get_row shape
  from coupling.bend, whose read laws are proved); sweep_row_nth /
  sweep_field_nth; the row-major flat_nth brick (the one new arithmetic:
  (1n+i)*w + j = w + (i*w + j)); the column->row assembly law
  (col_to_row: row i field j == column j's i-th element).
- sweep_ok gains a row-shape conjunct (every row has exactly w_params
  fields); the width bound stays at 8 for the current engine.
- the JSON sweep ingress follows (columns; total decode; the
  json_read_fresh analog).

## Gap inventory 2026-10-05 — arbitrarily complex models and sweeps

Honest backlog for "arbitrarily complex multi-network multi-dt models and
arbitrarily complex parameter sweeps" (each is a small law family in the
established pattern, unless marked FUNDAMENTAL):

Config/model side:
1. Non-integer dt ratios (dt 0.07 vs 0.1) — FUNDAMENTAL scope limit: the
   router is Nat-period by construction; arbitrary ratios need rational
   time + interpolation-phase laws (a bigger formal object, not a law gap).
2. Per-subnet integrators/schemes (and stochastic variants with per-sim
   seed routing) — the validator knows nothing of the scheme dimension.
3. n_svars per subnet unvalidated (cvar counts are; state-var counts not).
4. Coupling-function variety: only the Linear leaf is pinned
   (cfun_linear_order); sigmoidal pre/post variants need their own pins.
5. cvar name-resolution (the 'y1'->'xi' mapping resolved per model) — the
   sweep's sw_name_slot analog at the config level.
6. Delay units: ms -> source-step conversion + rounding is unpinned
   (off-by-rounding shifts causality silently).

Sweep side:
7. Structural sweeps (per-sim connectome/model/integer params) — rows are
   F32 scalars; needs a variant payload type.
8. Grid sweeps (cross-product of independent ranges) — columns vary
   together per row; a grid needs the row = grid-point construction.
9. Output un-routing: which slice of the concatenated output belongs to
   which subnet x sim (the demos' per-subnet extraction) — the reverse
   routing, slice_nth-shaped. Arguably the most user-visible gap.
10. Monitor variety: tavg covered (count + ZOH); BOLD and per-subnet
    monitor periods not.

Also of record: the demo's parallel-vs-sequential bit-exactness TEST is
the engine mirror of fan_gather_order's LAW.
