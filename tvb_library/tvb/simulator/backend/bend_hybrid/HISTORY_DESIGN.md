# History design: the tape is the spec, the ring is a proved compression

Decision record, 2026-10-02, after the tier-1 closure (109 laws). Written
before any history code exists; this file is the "why" behind the law
statements that follow.

## The question

A node's coupling input must be traceable to the right (source, delay,
weight, index): "the delay a lane receives really is the weighted output of
another node in another lane." The routing half is proved (indices, freshness,
non-aliasing, write uniqueness). The missing half is *value provenance*:
where the numbers handed to the leaf kernel come from. That needs a history
object in the law layer -- and histories in TVB engines come in two shapes:

- **A. the tape** -- append-only, addressed by absolute index (the chunked
  backends' semantics; the tinygrad-in-Bend FTree pattern);
- **B. the ring** -- flat buffer of capacity `cap`, write cursor at
  `n mod cap` (the compact engine artifact).

## The decision

**A is the semantics; B is a compression of A, settled by one theorem.**

1. All provenance laws are stated and proved against the tape (A):
   - *read-after-write*: writing `v` at index `n` then reading at `n`
     returns that leaf, at any depth;
   - *IC region*: reading below the first write returns the initial-condition
     leaf;
   - *stability*: writes above `n` never change what reads at or below `n`
     return;
   - *pruning corollary*: dropping the tape below `n - horizon` is
     observationally invisible -- the bounded recent past is semantically
     sufficient (the TVB chunk discipline, as a theorem rather than an
     assumption). This also retires the "tape = unbounded memory" objection:
     the proved object is a sliding window.
2. The engine keeps its flat ring (B), and the bridge is a single
   correspondence theorem: *a buffer of capacity `cap >= horizon`, written at
   `n mod cap`, returns the same leaf as the tape for every index in
   `[n - horizon, n]`*. Paid once, in one induction over one lap of the
   buffer; `cap >= horizon` enters `ok` as a config conjunct exactly like
   the existing `horizon` witnesses. Negative control `bad_ring`: an
   under-capacity ring, where the aliasing is real and the claim must be
   rejected (same discipline as `bad_alias`).

## Why not B directly

- **Compounding law tax.** Every index law against a ring carries `mod cap`
  side conditions; every future law inherits them. `read_distinct`-style
  claims become lap-arithmetic lemmas; the deferred `div_mod` debt comes due
  immediately for no spec-level gain.
- **The router already speaks the tape.** `router.bend` has no `mod`
  anywhere; `fits_lt`, freshness, window span are absolute-index theorems
  that plug into A unchanged.
- **Parallelism.** An FTree is forked to parallel branches at zero cost; a
  ring is one affine value threaded sequentially -- a composition point that
  fights the proved pointwise/list-local tick (`lanes_step_local`,
  `route_pointwise`).
- **B's only edge is constant memory, which A matches** once the pruning
  corollary exists (keep `horizon + margin` leaves, drop the rest).

## Float policy (recorded here on purpose)

Bit-exactness is out of the law layer's scope; relative-tolerance
differential testing stays the numerical referee. The laws guarantee
*traceability* -- every operand is the right leaf, from the right source,
at the right index, in the right order -- which is precisely what makes a
relative-tolerance comparison meaningful.

## What this unlocks, in order

- Link 2: blend wiring -- the `x0/x1/alpha` handed to `blend` are exactly
  `hist[src][line.i0]`, `hist[src][line.i1]`, `num/den`, for the line the
  proved router produced for that edge.
- Link 3: CSR slice -- the edge list folded by `gather` for target `t` is
  exactly the config's rows between `indptr[t]` and `indptr[t+1]`.
- Link 4 (capstone): for every config passing `ok` + `csr_ok`, at every tick,
  the coupling input of every target is the CSR-ordered fold of
  `w * blend(...)` over exactly the configured (src, delay, weight) triples.
  Structure and provenance, machine-checked; values, differential-tested.
