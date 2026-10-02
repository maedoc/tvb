# Bend engine notes — operational gotchas and proof-system facts

Durable notes for working on `bend_hybrid/` (the Bend Montbrio hybrid prototype).
Written 2026-10-01 after the first end-to-end port. For the *design* and the
*measurements*, see `README.md`; this file is the "how do I not get stuck"
companion.

## Toolchain

- Bend is at `/home/duke/.bend/bin/bend` (v2.0.34). `which bend` finds nothing.
- Lean 4.34.0 via elan (`~/.elan`), symlinked into `~/.local/bin` because
  non-interactive shells do not source `~/.profile`. Needed for
  `bend PROOF.bend --verdict`; without it that command errors on a missing kernel.
- Build: `/home/duke/.bend/bin/bend montbrio_sweep.bend -o montbrio_sweep`
  (~3 s). Runtime flags: `--threads N`, `--gpu off`.
- Python for the drivers: `tvb_library/.venv/bin/python` (numba 0.68, numpy 2.5).
  System `python3` has no numpy.
- `bend PROOF.bend --verdict` prints `ALL PROOFS CHECK` for the current laws.

## Syntax traps that cost the most time

- `-> IO(X)` uses parentheses for **return types**; `do IO<X>:` uses angle
  brackets for **blocks**. Mixing them is a parse error.
- A bare run of `IO.print(...)` statements is a parse error — they must live in a
  `do IO<Unit>:` block, and a block with a non-Unit result needs an explicit
  `return`, which *wraps a pure value*: bind the effect with `<-` first, then
  `return` the bound name.
- One `match` per def. Several values at once: `match a b:` — and the scrutinees
  must be in **binder order**, not the order you want to read.
- A `match` inspects only parameters and pattern bindings, never computed values
  or plain locals. If a `let` precedes a `match` on a parameter, it is rejected.
- No `if`: match on `True{}`/`False{}` or `Bool.pick(T, c, a, b)` — and
  `Bool.pick` consumes **both** branches, so a value used in either is used twice.
- Negative literals must be `F32.neg(x)`. Operators need a type annotation
  (`(a * b : Nat)`), so the arithmetic uses `F32.add`/`mul`/`div` — which is also
  exactly the `-ffp-contract=off` discipline the C++ core needs.
- Everything is affine by default: a `let`/parameter may be used once. `+` marks
  it reusable, which requires `Data`. **An `Array` is `Type` (single owner) and
  can never be `+`** — always thread it. A record holding arrays is `is Type`.
- Defs must be defined before use; **no mutual recursion**. Flat multi-cons
  patterns (`case b0 <> b1 <> b2 <> b3 <> t:`) and `Maybe.default(a, A, m, d)`
  are the workarounds for what would otherwise need mutual recursion.
- Termination needs a **shrinking argument first**; everything after it is free.
  Counted loops thread a remaining count first, since the index grows.
- `Array.get(T, a, i)` returns a dependent pair `Array<T> & T` and needs `T`
  spelled out. The pair can only be destructured as a *parameter*, so a fetched
  value cannot be read and used in the same call — see the prefetch note below.
- Dependent return types across a module boundary do not normalise. Keep a decider
  and its lemmas in **one file**.

## Proof system, precisely

- `{==}` is *structural* reflexivity. Integer arithmetic and structural defs
  (`Nat.add`) normalise; **primitives on symbolic args do not**. So quantified
  laws work over `Nat` and structural ops, and **not** over `U32`/`F32`.
- No float value equality is provable — not even `F32.add(0.0,0.0) == 0.0`, and
  not `F32.is_lt(1.0,2.0) == True{}`. There is also **no `F32.cmp`**, so floats
  have no total-order value at all.
- Ordering is not a proposition (`<` is Bool-valued). The workaround that works:
  make decidability return a **Type** — `le_ok a b` is `Unit` iff `a <= b`,
  `Empty` otherwise — so `le_ok(a,b)` *is* the proposition. `le_ok` must be
  right: I got it wrong twice (`1n+p <= 0` and `0 <= 1n+p`), and a wrong decider
  silently accepts false claims. **Always keep a negative test in the same file**
  (`x < x` must be rejected) — that is the only thing that catches it.
- Cross-module `Laws.x` in a dependent return type silently breaks; single file.

## Runtime facts (measured on this machine, 8 cores, no CUDA)

- **`IO.spawn` is exactly serial** for pure work (1 pt 206 ms, 2 pts 432 ms, 8 pts
  1412 ms = `n * t`). Parallelism comes from nested parallel lets
  (`a b = f(x) g(x)`), two levels deep for 8 points: 1412 ms → 431 ms.
- Fork-join per **node** is 5.7× *slower* (53 ms → 300 ms at 1→8 threads):
  per-node work is ~5 µs. Do not fork inside a step.
- `--gpu off` / no GPU runs bangs on the CPU pool. A `!` ships a 16384-lane cube;
  aim 4⁷ leaves, one per lane. The ring is a single-owner `Array`, so it cannot be
  shared across a fork — a GPU port would need the forkable snapshot-list history
  that was deliberately rejected for CPU speed. Read `bend guide shaders`.
- Arrays must have a power-of-two size; indexes wrap, which is why a ring of
  `next_pow2(max_delay+1)` is safe (every slot is pre-filled with the IC).

## Data plane

- Bend cannot bit-reinterpret floats (`F32.to_u32` is a numeric truncation), so
  the job file carries raw u32 words and floats as scaled integers (÷1e6), and
  `e.g. JOB_HISTV` must be filled from the **v** ICs (getting this wrong is silent).
- `F32.show` is **not** round-trip exact (~7 digits), so the trace channel carries
  `round(value * 1e6)` as integers. Comparing text floats produced a phantom
  1-ulp "failure".
- Each bulk section lives in its own file: an `Array` decoded from it is
  single-owner and must have exactly one consumer.

## Traps that produced real bugs (all four found numerically, not by proofs)

1. History read lagged one edge — a consequence of the `Array.get` pair rule;
   fixed with a two-step prefetch of the packed edge word. Debug trick: set all ICs
   and `w[e] = 100*(e+1)` so each row's coupling *is* the edge list it summed.
2. Seed address hard-coded `t = 1`, so from step 2 the first CSR row read the
   wrong slot while every other row was correct.
3. The tick advanced in the coupling pass, but the update pass reads `t` for the
   trace index and push slot — both off by one from step 2.
4. `cv` is a model **parameter** (`cr * C_r + cv * C_V`), and MontbrioPazoRoxin's
   default is `cv = 0.0`. A job with `cv = 1.0` disagrees with the reference by
   ~20 % and still looks plausible.
5. Measurement trap: a `@nb.njit(cache=False)` kernel rebuilt per call re-JITs
   every point and inflates the numba baseline ~4×. Memoise it.
## Router (2026-10-01, second session)

- `router.bend` is a Bend-NATIVE design (carried per-lane counters, not the
  template's closed-form div/mod): Lane{k, left, newest}, `steps`/`step_lane`,
  `route_read` (the only place the ZOH clamp lives), `route_window` (Q2),
  `tick` over the whole config tree, Bool validators (`ok`), and the
  le_ok/lt_ok deciders for witness-carrying constructors.
- Laws: `LAWS_router.bend` (human file), proofs `PROOF_router.bend`;
  `tests/run_router.sh` is the full gate (proofs --verdict + bad/ negative
  controls + pinned functional tests).
- New idioms learned (beyond the traps above):
  - law binders reused in a proof are marked `+` IN THE LAW (`for +t: Nat`);
    the proof def's params stay bare (`def Laws.x(t, n):` -- `+` there is a
    parse error).
  - succ-pattern binder reuse is `1n++q`.
  - `%e : P` rewrites RHS-of-e to LHS-of-e in the goal; simplifying X to X'
    therefore needs `Equal.sym(Nat, X', X, lemma)`. `Equal.sym(A, a, b, e)`
    takes `e : {a == b}` -- argument order matters, the error message names
    the expected equation.
  - Nat arithmetic on symbolic args only reduces when the FIRST argument is
    the scrutinee: write `1n+n`, never `Nat.add(n, 1n)`, in anything a proof
    must see through. `Nat.cmp(q, 0n)` is also stuck on symbolic q -- match
    one level deeper.
  - hypotheses ride along as law binders: `for +h: {check(x) == True{} : Bool}`
    (bendygrad pattern); eliminate `{False==True}` with Bool.fne + a motive.
  - `List<&2, T>` is the Data-kinded list (`&2` = Data); plain `List<T>` is
    Type-kinded and breaks `is Data` records.
  - pairs destructure awkwardly; a `type Tick is Data` record with accessors
    is nicer than `A & B` for multi-result defs.
  - do-IO blocks take `<- IO.pure(...)` binds; pure lets live outside.
  - string append is `++`; `String.concat` takes a LIST.
  - a cons literal in a `let` needs a type annotation: `{x <> Nil{} : List<&2, T>}`.
- Reference implementation of all of the above: /tmp/bendygrad (KapioKai's
  tinygrad port, 32 proved laws) + its PORTING_RULES.md.

## Router laws, second expansion (derived from the template itself)

- 14 new laws (30 total, gate green): arithmetic (add_one, add_sub_succ,
  eq_refl_b, ne_succ), CONTROL FLOW (due_publishes, lane_hold,
  due_iff_publishes, run_segmentable, countdown_publish, period_from_init),
  CSR data structure (csr_ok + 4 reject instances).
- `run_segmentable` IS nb_hybrid's chunking comment (~L1642: "correct
  regardless of how many steps a chunk spans") as a lemma.
- `csr_ok_bad_delay` IS nb_hybrid's horizon ValueError (~L1656) as a
  rejected claim.
- BUG FOUND by the method: `nats_last` originally returned 0 for every list
  (recursed to Nil and dropped the element). The POSITIVE instance law
  (csr_ok_good) caught it; the negative ones passed vacuously. Lesson:
  positive instance laws are load-bearing, not decoration.
- New idioms: pattern binder reuse in one arm only (`1n++q`); Equal.sym(A,
  a, b, e) takes e:{a==b} and yields {b==a} -- get the order wrong and the
  error names the flipped equation; law binders reused in proofs are `+` in
  the LAW, bare in the proof def.
- Template facts worth laws next: horizon is per-SOURCE lane (shared
  srcbuf), not global; coupling+stimulus are computed EVERY master tick but
  consumed only at due ticks (odd-tick values feed only ctavg); noise is
  master-grid indexed (subsampled for slow lanes).
