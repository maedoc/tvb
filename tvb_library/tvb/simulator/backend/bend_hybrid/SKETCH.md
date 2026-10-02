# Bend implementation sketch — `cpp_hybrid` simulator backend

A design + illustrative-code blueprint for a Bend port of
`tvb/simulator/backend/cpp_hybrid/_core.cpp` (the compiled nanobind hybrid
simulator core) plus the dfun codegen layer in `dfungen.py`.

This is a **sketch**, not a working plugin. Bend (`bend` binary) is not
installed in this tree, so the `.bend` sample is written to documented Bend
idioms but is not compiled/tested. It is meant to be read side-by-side with
`_core.cpp` to check the mapping is faithful before any real porting effort.

---

## 0. What the C++ does (recap, from `_core.cpp`)

Per master step `t`:

1. **Zero** each subnet's coupling scratch `c`.
2. **Apply projections** (`proj::apply`): for each directed edge read the
   *source history* slot `t-1-delay` (interpolating for multi-dt), apply a
   per-edge **pre** transform (`cfun_pre`), accumulate the weighted sum into a
   per-target-node `cx`, apply the **post** cfun (`cfun_post`), scale by
   `scale*ts` and add into the target subnet's `c[tgt_cvar]`.
3. **Per subnet**: add stimulus into `c`; if this is the subnet's tick
   (`(t_abs+1) % K == 0`), do a Heun or Euler step (dfun twice for Heun),
   clamp, then `push_state` the new state into the `(…, H, W)` ring buffer.
4. **Accumulate** `tacc` (voi-spec sums over modes) and `cacc`, and feed the
   kernel-side monitor engines (`kmon::step_one`: Raw / Subsample / Bold HRF).
5. Normalize accumulators by the chunk count and emit.

State layout everywhere is `(n_svar, n_node, n_modes, W)` flat float32; the
**W dimension is SIMD lanes**. The dfuns and coupling math vectorize over W
via `-fopenmp-simd` (width-8). Generic models have their derivative
*expressions* translated to C++ (`dfungen.emit_sources`) and dispatched by id.

---

## 1. Numeric types (corrected 2026-10)

The sketch originally claimed Bend numbers are `f24` (a throwback to the *old*
HigherOrderCO Bend). **That is wrong for the Bend actually installed here
(`/home/duke/.bend/bin/bend`, v2.0.34).** Verified in `base.bend`:

```bend
type F32 is Data:
  F32{data: Word(32n)}
```

* `F32` is native IEEE-754 single precision — bit-identical to C++ `float`.
  Literal `1.5` is an `F32`; ops `add sub mul div mod` and `is_eq is_ne is_lt`.
* There is **no `F64`/double** type (`type F64` does not exist in `base.bend`).

Consequences for parity:
* **Bit-exact float32 parity IS achievable** for every pure-float path — all
  hand-written dfuns (`_core.cpp`), Heun/Euler combining, coupling arithmetic
  that stays in `float`.
* **The residual risk is narrow and inverted:** `_core.cpp` deliberately
  promotes a *few* terms to `double` — `cfun_post`'s sigmoid/SJR bodies
  (`(float)((double)p + …)`), the Zerlaut `z_TF` chain, and CerebellarMF's
  `crbl_fluct_*`/`crbl_TF_*` (fully double). With no `F64` in Bend 2.0, those
  specific double-precision terms degrade to F32 (single) — tolerance-level on
  *those* spots only, not the whole backend.
* Optionally, F64 can be *emulated* (two-word / `hi`,`lo` F32 pair) for the
  handful of promoted sites if exact parity there is hard-mandated — note it as
  a spike, not the default.

There is also a real `Array<-T: Type>` — a balanced binary tree with
`Array.get(a, i)` / `Array.set(a, i, v)` at O(log n), `Array.new(d, v)`,
`Array.map`, `Array.join`, `Array.swap`. That is an O(log n) answer to the
history-buffer question, better than the cons-list sketch first proposed
(see §5.2): the `(…, H, W)` ring buffer becomes an `Array<Cell>` indexed
by `U32.and(t, H-1)`.

## 2. The core thesis: where Bend and the C++ disagree

The C++ gets parallelism from two places that Bend does **not** have:

| C++ mechanism | Bend reality | Consequence |
|---|---|---|
| Fix a batch of `W` SIMD **lanes**, vectorize every kernel over them | Bend has no explicit SIMD lanes; parallelism is **implicit, over the data structure** | **Drop `W` entirely.** The `for (int i = 0; i < W; i++)` inner loops disappear; each `(node, mode)` becomes a parallel leaf instead. |
| Mutable in-place flat arrays (`float* x`, ring buffer `buf`) with O(1) indexed writes | Bend is **immutable, pure, tree-based**. No O(1) mutable random-access buffers. | State and history must become **functional trees**; mutating a single slot = re-linking on the path to the root (persistent data structures). |
| `push_state` ring slot `t & (H-1)` | no allocation/ring of nodes | History = a **persistent stack/ring of full state snapshots**; delays read by walking back `delay` steps. |

**The good news:** the *computational core* of a hybrid simulator — dfun
evaluation, Heun combining, and the sparse coupled matvec — is a pure map /
fold over nodes, which is exactly Bend's sweet spot. The dfuns are
embarrassingly parallel over `(node, mode)`. The coupling is a per-target-node
reduction over in-edges. Both map cleanly to `bend`/`fork`/`for`.

So the port keeps the **same per-step algorithm** but re-expresses it in a
data-parallel, immutable vocabulary.

---

## 3. Naming & the selection of what changes shape

### 3.1 `W` disappears
`add_subnet(width)` and every `W`-stride vanish. A subnet is described by
`(n_node, n_svar, n_parm, n_cvar, n_modes, model_id, K, dt, H)`.

### 3.2 State as a tree of nodes
Replace `float x[(n_svar, n_node, n_modes, W)]` with

```
node -> mode -> svar -> F32 value
```

Because a dfun uses *all svars of one node-mode*, the natural (cache- and
reduction-friendly) node is a mode whose child is a *vector of svar values*:

```bend
type Mode = M { xs: SVec }            # one mode of one node's state
type SNode = N { modes: (SNode, SNode) ... }
```

For the sketch we flatten: a subnet state is a **Tree balanced over "unit
cells"** `(node, mode)`, each cell a tuple of `n_svar` `F32` values. The shape
(the svar count, n_parm, …) is carried separately (it must be implicit in the
tree for map/fold).

### 3.3 Params, coupling, connectors
Same cell-centric idea:
- `parr`  → per-(node) vector of `n_parm` `F32`.
- `c`     → per-(node, mode) vector of `n_cvar` `F32`.
- `src_cvars`/`w`/`idx`/`ptr` → a **sparse Connector**: `(ptr, idx, w,
  del, src_cvars, cfun_id, cfp, scale, ts, …)`, exactly the fields of C++
  `struct proj`.

---

## 4. Dfun kernels (the parallel core)

Each dfun becomes a **pure function** `dfun : cell -> DCell` — the entire C++
`for (int i=0;i<W;i++)` body, run once per `(node, mode)` in parallel. The MPR
example, verified in `sketch.bend`:

```bend
def dfun_mpr(+c: Cell, +p: Parms, +cr: F32) -> DCell:
  +tau : F32 = parm_tau(p)
  # ...
  # C++ `r = r0 * (r0 > 0)`, kept as a multiply by the 0/1 mask: identical float
  # semantics (a branch would diverge on NaN/inf, a multiply does not)
  +r : F32 = F32.mul(r0, U32.to_f32(Bool.to_u32(F32.is_gt(r0, 0.0))))
  # dr = (Delta/(PI*tau) + 2*r*V)/tau
  dr = F32.div(
    F32.add(F32.div(delta_p, F32.mul(F32.pi(), tau)),
            F32.mul(F32.mul(2.0, r), v_m)), tau)
  D{dr, d_v}
```

Because Heun needs `dfun` at `x` **and** at `xi`, and both reads are pure,
Bend evaluates them as independent parallel subtrees — no extra scratch
buffers (`dx`, `xi`, `dxi` in C++) are needed:

```bend
def heun_cell(+c: Cell, +p: Parms, +cr: F32, +dt: F32) -> Cell:
  +d1 : DCell = dfun_mpr(c, p, cr)
  xi = clamp_mpr(axpy(c, d1, dt))
  +d2 : DCell = dfun_mpr(xi, p, cr)
  m = mk_dcell(F32.mul(0.5, F32.add(dcell_dr(d1), dcell_dr(d2))),
               F32.mul(0.5, F32.add(dcell_dv(d1), dcell_dv(d2))))
  clamp_mpr(axpy(c, m, dt))
```

A full step is then a **parallel let** over the two halves of the state tree
(Bend 2.0 has no `bend x = e:` block binding — parallelism is `a b = f(x) g(y)`
inside a recursive def):

```bend
def step_tree(s: State, +p: Parms, +cr: F32, +dt: F32, +heun: Bool) -> State:
  match s:
    case Leaf{+c}:
      step_leaf(c, p, cr, dt, heun)          # match on True{}/False{}: no `if`
    case Node{l, r}:
      nl nr = step_tree(l, p, cr, dt, heun) step_tree(r, p, cr, dt, heun)
      Node{nl, nr}
```

**Generic models (the `dfungen` layer):** Bend has no string→function JIT. The
exact analog of `dfungen.emit_sources` is a **codegen pass that emits a Bend
`def dfun_<id>(...)` per expression model**, plus a dispatch tree pattern over
`model_id`. The `cp312`/ctypes runtime fallback (`generate_lib`) has **no** Bend
equivalent — Bend is compiled, not dynamically loadable without a compiler at
runtime. In a Bend port every model must be compiled in at build time (closer
to the built-in table than to the runtime fallback).

---

## 5. Coupling (sparse matvec) — the interesting part

### 5.1 Without delays / multi-dt (the "fast path" of `proj::apply`)
For each target node `j`, sum over in-edges `nz in ptr[j]..ptr[j+1]` of
`w[nz] · src_state[idx[nz]]`, then `cfun_post`. This is a **dense-free sparse
reduction per target node** — `for`/`bend` over the edge lists:

```bend
def apply_one(cell_tgt, conn, src_state, scale, ts):
  acc = zero_cvector(n_cvar)
  # per edge, read src value for each src_cvar, apply cfun_pre, w*fold
  for edge in conn.edges: acc = w*read_pre(...) + acc
  cpost = cfun_post(acc, conn.cfp)
  cell_tgt.c += scale*ts*cpost
```

### 5.2 The history buffer: solved by `Array`, not by cons lists
This section originally concluded the ring buffer "does not port" and proposed
a cons list of snapshots with an O(`delay`) ancestor walk. **That was wrong**,
and reading `bend base` settles it: Bend 2.0 has a real `Array<-T>` — a
balanced binary tree with

| op | signature | cost |
|---|---|---|
| allocate | `Array.new(T, d, v)` | O(2^d) once |
| write | `Array.set(T, a, i, v)` (sugar `a[i] <- v`) | O(log n), in place |
| read | `Array.get(T, a, i)` | O(log n), returns `Array<T> & T` |
| map / join | `Array.map`, `Array.join` | parallel |

Indexes **wrap around**, so the C++ ring's `t & (H-1)` is literally
`U32.and(t, H-1)` with `H` a power of two — the same assumption `_core.cpp`
already makes. So:

```bend
def push_state(hist: Array<Cell>, t: U32, cell: Cell) -> Array<Cell>:
  Array.set(Cell, hist, U32.and(t, 7), cell)

def read_cell(p: Array<Cell> & Cell) -> Cell:
  # Array.get hands the array back beside the element; a match must scrutinize a
  # parameter, never a computed value -- hence this one-line helper.
  match p:
    case (hist, +c):
      c

def read_state(hist: Array<Cell>, t: U32) -> Cell:
  read_cell(Array.get(Cell, hist, U32.and(t, 7)))
```

This is checked and runs (`sketch.bend`, section "The history ring").

Two constraints follow from `Array` being a `Type` (single owner, not `Data`):

* **An array cannot be copied or cloned.** A read hands it back, so a read is a
  linear chain; two independent readers need two rings (or one reader threaded
  by hand). This is the sharpest porting constraint on the monitors and on
  anything that reads the same history twice.
* `Array.set`/`Array.get` want the element type passed explicitly
  (`Array.set(Cell, ...)`) — inference does not pick it.

Multi-dt interpolation (`alpha`, `s0/s1`, zero-delay `alpha=0`) is unchanged:
still two slot reads plus the same blend, now two O(log H) lookups.

### 5.3 `globalT` (PreSigmoidal dynamic)
Mean of a source cvar over **all** projection edges, per source-mode, stored in
`gthr` before the loop. In Bend this is a single reduction over the edge list
(`for`) computed once and passed to the per-edge pre as an extra input — no
scratch array needed.

---

## 6. Monitors (Raw / Subsample / Bold)

The `kmon::step_one` state is *also* mutable in C++ (`interim`, `stock`,
`m_step`). In Bend:

- **Raw / Subsample:** stateless per step (just collect/decimate rows). Trivial
  to keep as an accumulated output list.
- **Bold** needs the interim ring `(interim_istep)` then the outer stock
  `(stock_steps)` then an HRF dot with a rolled index. Port as:
  - interim = a bounded *list* of the last `interim_istep` rows (cons + cap),
  - outer stock = same bounded-list pattern,
  - HRF dot = a `for` reduction once per monitor period.
  The `(q - r) % S` roll is an index into a persistent list (or stored as an
  explicit cyclic rotation), not an array subscript.

Note the C++ kernel monitors require `chunk_size == 1`; the Bend port keeps
that constraint identically. `tacc`/`cacc` chunk normalization carries over
(logical per-chunk mean, division by real count).

---

## 7. Master control loop

C++ is an imperative `for step in 0..nstep` inside a GIL release. Bend
expresses time as a **recursive functional stream** (each step = a pure
function of the previous world state):

```bend
def run(w: World, nstep: Nat) -> World:
  # the C++ `for step in 0..nstep` becomes a structural recursion on the step
  # counter; Bend verifies termination from the match on Nat
  match nstep:
    case 0n:
      w
    case 1n+p:
      # 1. zero coupling, apply projections, add stimulus -> c'
      c2 = coupling_pass(w)
      # 2. per subnet: tick? integrate : hold, in parallel over subnets
      s2 w2 = step_subnets(w, c2) step_subnets(w, c2)
      # 3. push each subnet's new state into its ring (Array.set, O(log H))
      # 4. monitors + voi/c accumulators
      world2 = observe(rebuild(w, s2, w2), c2)
      run(world2, p)
```

`run` is a tail-recursive fold over steps — Bend will parallelize *within* a
step (all nodes, all subnets, all edges) while the temporal direction stays a
sequential recurrence (correct: it *must* be).

---

## 8. Bend 2.0 idioms this design depends on (all verified against `bend` 2.0.34)

The first draft of this file was written from memory of the *old* HigherOrderCO
Bend and invented syntax that does not exist. Everything below was established
by running `/home/duke/.bend/bin/bend` (`bend guide`, `bend base`,
`bend <file>`) — `sketch.bend` in this directory checks and runs, and each item
has a live example there.

| you want | Bend 2.0 actually gives you |
|---|---|
| explicit SIMD lanes / parallel bindings | **parallel let**: `a b = f(x) g(y)` inside a recursive def. There is no `bend x = e, y = e:` block. |
| `if cond: a else: b` | **no `if` at all.** `match b:` on `True{}` / `False{}`. |
| `x.field`, `c.r` | **no field access syntax.** Fields are read by `match` on a *parameter* (or a pattern binding), never on a computed value or a plain local — so every field read needs its own one-line accessor def. This is the largest recurring cost of the port. |
| `Foo{a: x}` | constructors are **built positionally**: `D{a, b}`; named fields exist only in *declarations* and *patterns*. |
| `a + b`, `-1.0` | operators **demand an explicit type**: `(a * b : F32)`. In practice this means writing `F32.add`, `F32.mul`, `F32.div` verbs — which is a happy accident, because one call per operator is exactly the `-ffp-contract=off` discipline `_core.cpp` needs for bit-exactness. |
| sequences of IO steps | must live in `do IO<Unit>:` — a bare run of `IO.print` lines is a parse error. |
| `f24` numbers | `F32`, bit-identical to C++ `float` (§1). |
| mutable arrays | `Array<-T>`: `Array.new`, `Array.set`, `Array.get`, `Array.map`, `Array.join`, wrapping indexes. `Type`-kinded, so **never copyable**. |
| shadowing a parameter | no: every `let`/parameter is **affine** (used at most once). Anything read twice needs `+` (only for `Data`), and float literals need a context type: `+x : F32 = 1.0`. |
| `law f: ...` proofs | exist, and `bend PROOF.bend` is the gate — but `--verdict` needs Lean v4.34 (not installed here), so a Bend port cannot currently self-verify by kernel re-check. |

Design consequences worth stating plainly:

* **The `+`/affine discipline is pervasive.** A dfun that reads a state var
  three times needs `+` on that binding; parameters of `struct proj` that feed
  both the pre and post cfun must be `+`. It is mechanical, but it is why the
  port wants *generated* per-model code (the `dfungen` analog) rather than
  hand-written dfuns.
* **Field accessors do not vectorize by accident** — each is its own call, so
  a dfun's inner loop is a chain of small defs. Worth measuring before
  committing to the port.

---

## 9. Layout / proposed package structure

Mirror the existing backend dir naming:

```
tvb_library/tvb/simulator/backend/bend_hybrid/
  __init__.py       # BendHybridBackend (parallel to backend.CppHybridBackend)
  lib/
    core.bend       # coupling, stepping, monitors (reduced/driver portion)
    dfuns.bend      # hand-written kernels (MPR, G2D, Kuramoto, ... )
    gen/            # generated dfuns (dfungen equivalent, emitted at build)
  dfungen.py        # expression -> .bend def dfun_<id> (...)
  backend.py        # mirrors backend.py, calls into the Bend runtime
  SKETCH.md         # this file
```

The Python `backend.py` (buffer orchestration, model-id selection,
`generic_model_table`, parameter packing) maps **unchanged** in spirit — Bend
substitutes for the compiled extension + ctypes fallback layer only. The
27-model support matrix, id ranges (0..12 hand-written, 100+ built-in generic),
and the disjoint-range/gap-padding rules all carry over unchanged; the only
difference is there is no `125+` runtime-fallback range (Bend cannot JIT).

---

## 10. Faithful-parity checklist vs `_core.cpp`

- [x] Layout `(node, mode, svar)` (drops `W` and the flat strides).
- [x] `dfun_*` bodies line-for-line (MPR clamp `r*(r>0)` kept; all literal
      constants — `M_PI_F`, `1.4142135623730951f`, `2.718281828459045`,
      epsilons `1e-6/1e-9/1e-15` — kept as float literals).
- [x] Heun coupling-fixed-across-stages (coupling read once, reused for both
      dfun calls).
- [x] Multi-dt tick gating `(t_abs+1)%K==0`, and the read rule
      `tau=(t1-1)/K-delay`, `s0/s1`, zero-delay `alpha=0`, IC-prefill.
- [x] Cfun pre/post ids `-1..9`, scaling by `scale*ts`.
- [x] `globalT` mean-over-edges path.
- [x] voi-specs: kind 0 = state var, kind 1 = var difference, summed over modes.
- [x] chunk normalization by real count (partial final chunk).
- [x] Monitor engines require `chunk_size == 1`.
- [x] Ring history -> `Array<Cell>` with `U32.and(t, H-1)` (§5.2), matching the
      C++ ring exactly rather than the cons-list first guess.
- [~] Bold interim/stock rings -> bounded lists (§6); note that `Array` is a
      single-owner `Type`, so a monitor that reads its ring twice needs either
      two rings or a threaded read.
- [x] Monitors: the `first_order ? (acc-1)*k1v0 : acc` and HRF roll kept.
- [x] Model id dispatch + gap padding (built-in range only; no runtime range).- [x] float32 exactness / `-ffp-contract=off`: **Bend 2.0's `F32` is IEEE-754
      single precision, bit-identical to C++ `float`** (see §1) — so bit-exact
      parity is *achievable* for every pure-float path. **Caveat:** `_core.cpp`
      promotes a few terms to `double` (cfun_post sigmoid/SJR, Zerlaut
      `z_TF`, CerebellarMF `crbl_*`); Bend has no `F64`, so those specific sites
      degrade to tolerance-level parity. That list is the acceptance risk now —
      it is finite and enumerable, not global.

---

## 11. Open questions — answered by the prototype

These were the open questions when this sketch was written. The prototype in
this directory (`README.md` has the measurements) answers all six; they are kept
here so the reasoning that led to the design is still legible.

1. ~~f24 precision~~ — **resolved**: `F32` is float32. The follow-up (tolerate
   on the `double`-promoted sites, or emulate F64) resolved to *tolerate*:
   `nb_hybrid`'s generated kernel evaluates parts of the drift in float64 and
   rounds once into the float32 state, and Bend has no F64. Measured cost:
   `r` matches the reference **exactly** over 300 steps, `V` to 5e-07.
2. ~~keep `W`?~~ — **dropped**. It bought nothing numerically once `F32` was
   confirmed, and the prototype's parallelism comes from forking across sweep
   points instead.
3. ~~history representation~~ — **resolved**: `Array` with wrapping indexes,
   O(log H), and the ring's power-of-two size is larger than the C++ ring's
   `max_delay+1`, which is harmless because every slot is pre-filled with the
   initial state. The "several rings for Bold" sub-question stands, and is now
   listed as a limitation rather than a blocker.
4. ~~first model subset~~ — **MontbrioPazoRoxin**, for the reason nobody
   predicted: in this fork that class *is* the 2-variable bistable oscillator,
   so the prototype's drift was already written before the question was asked.
5. ~~packaging~~ — **native binary + a Python wrapper**. The emitted C is a
   whole `main` with every def `static` (a toy def's name appears zero times in
   the output), so a CPython extension is impossible without patching the
   compiler's emitter. The subprocess boundary is real and costs nothing: the
   crossing happens once per sweep point, not once per step.
6. ~~laws/proofs~~ — **Lean v4.34.0 installed**; `bend PROOF.bend --verdict`
   is a real gate and passes. It also settled a question the sketch did not
   anticipate: Bend 2.0's `{==}` is *structural*, and float values never
   normalise, so **no float value equality is provable**. The laws are therefore
   structural and integer ones, and the numeric claims live in
   `compare_montbrio.py`.

Two questions this sketch did not ask, which the prototype answered the hard
way:

* **`Array.get` returns a dependent pair, and `match` only inspects
  parameters.** A fetched value therefore cannot be read and used in the same
  call — it must be carried into the next call as a pair, which delays it by
  one iteration. This is the deepest constraint in the port; it caused the
  history read to use the previous edge's address until a two-step prefetch
  fixed it.
* **`IO.spawn` does not fan pure work out** (measured exactly serial, `n * t`).
  Bend's parallelism is the parallel let `a b = f(x) g(x)`, nested.
