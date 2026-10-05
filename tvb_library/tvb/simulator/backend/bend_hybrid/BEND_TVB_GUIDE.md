# Writing Bend for TVB — a working guide

> **New here?** Start with [README.md](README.md) — the guided tour (goals, data structures, the high-level laws). This file is a deep dive.

Collected 2026-10-01 from the first end-to-end port (MontbrioPazoRoxin hybrid
kernel with a delayed connectome and a sweep). Companion documents:

- `NOTES.md` — syntax and toolchain traps. Look things up there.
- `README.md` — the prototype's design, measurements, and explicit limits.

This one is the *judgement*: which parts of a TVB hybrid simulation Bend is good
for, which it is bad for, and why — so you don't rediscover it by porting.

---

## 0. The lesson that cost the most

I answered "can Bend express `nb-hybrid-sim.py.mako`?" when the real question was
"what would a Bend-native TVB hybrid engine look like?". Those have opposite
answers, and the first one made Bend look useless for no good reason.

**Porting an existing kernel asks whether Bend can imitate it. Designing an
engine asks where Bend's actual strengths fall.** Decide per algorithm, never
per project or per language reputation.

---

## 1. Five facts to establish before designing anything

Verify each against the installed compiler; do not trust memory, including mine.

### 1.1 The language is not the Bend you remember

Installed here: **Bend 2.0.34**. The `f24`-only HigherOrderCO Bend is gone.
`F32` is IEEE-754 single precision, bit-identical to C++ `float`; there is **no
`f64`** and **no `F32.cmp`** (so floats have no total-order value at all).

### 1.2 The runtime is compiled C, not an interpreter

Measured: 100M `Array.get` = 85 ms, 100M `F32.add` = 85 ms — about **0.85 ns**
each. An early reading of "13 ns per get" turned out to be a measurement
artifact of a badly-shaped benchmark; it nearly convinced me the design needed
flat buffers. **Don't assume interpreter overhead; measure.**

### 1.3 Ownership is affine, and it is the deepest constraint

Every `let` and parameter may be used **once**. `+` marks a binder reusable and
requires its type to be `Data`. An `Array` is a `Type` — single owner — so it can
never be `+`, must always be threaded, cannot be shared across a concurrent
branch, and cannot be pooled between runs.

Consequences you will design around:
- a record holding arrays is `is Type`, so it too is threaded, never copied;
- anything `Data` (a `List`, a `String`, a config record) *is* freely copyable —
  which is exactly what makes it shareable across parallel lanes;
- you cannot "just reuse the history buffer" between sweep points. Measured cost
  of rebuilding per point: ~0.1 %. Tolerable, but not free.

### 1.4 Parallelism is a granularity argument, not a language feature

Everything below is measured on this machine (8 cores, no CUDA), workload
N=300 nodes, 300 steps, 89,700 edges:

| what you fork over | result |
|---|---|
| nothing (`IO.spawn`) | **exactly serial**: 206 / 432 / 1412 ms for 1 / 2 / 8 points |
| each sweep point (nested parallel lets) | **1412 → 431 ms**, and 331 → 69 ms per point at 8 threads |
| each node | **5.7× slower**: 53 → 300 ms going 1 → 8 threads |

`IO.spawn` gives you *concurrency of effects*, not parallelism of pure work.
Per-node work here is ~5 µs, far below the ~0.5 ms the fork-join scheduler wants
per task. **Rule: only fork where a task is ≫0.5 ms of straight-line work, and
measure before believing any claim about speed.**

### 1.5 The proof system is narrow, but not as narrow as it first looks

`{==}` is **structural** reflexivity. Integer arithmetic and structural defs
(`Nat.add`, which pattern-matches) normalise; **primitives on symbolic arguments
do not**. So:
- quantified laws work over `Nat` and structural ops;
- they **cannot** be written over `U32`/`F32` — `U32.add(x,0) == x` is unprovable;
- no float value equality is provable at all — not even `F32.add(0,0) == 0`.

The unlock is §4: make *decidability* return a `Type`.

---

## 2. Which parts of a TVB hybrid sim suit which backend

| layer | Bend verdict | why |
|---|---|---|
| drift / dfuns (`state_variable_dfuns`) | **opaque** | F32, unreducible. Keep the model's expression string as the spec. |
| CSR coupling gather + scatter | **hostile** | dense, uniform, branch-light. Fork-join per edge is ~1000× overhead; numba/C++ already vectorise it. |
| history ring / delay addressing | **neutral** | integer index arithmetic. Correct in either language; only provable in one (see §4). |
| multi-dt schedule, `k_j`, ZOH necessity, horizon sufficiency | **good** | combinatorics over integers — exactly what the proof system can check. |
| configuration validity (cvars, horizons, weights, sweeps) | **very good** | huge combinatorial space; illegal configurations become type errors. |
| monitor engines | **meh** | per-sample accumulation; provable indexing, but the HRF fold is sequential. |
| **parameter sweep over thousands of configurations** | **very good** | one flat loop per point, `Data` inputs, and the only shape that scales to the GPU's 16,384 lanes. |

Take-away: **Bend's leverage is the outer loop and the configuration algebra,
not the inner kernel.** A TVB "Bend engine" is credible if it is a verified
scaffolding around existing kernels plus a sweep driver — not if it is a
faster inner loop.

---

## 3. Numerical fidelity: literal transcription is the spec

TVB's drift is a *string* (`models/infinite_theta.py`):
`"r": "1/tau * ( Delta / (pi * tau) + 2 * V * r)"`. The numba kernel embeds that
string, so **its operator association is part of the observable behaviour**.
`(1/tau) * X` and `X / tau` round differently. Bend has no FMA to hide behind, so:

- transcribe term-for-term, left to right, one rounding per operator;
- use `F32.add`/`mul`/`div` rather than operators (which need annotations anyway);
- expect ~1e-7 residual against `NbHybridBackend`: its generated kernel promotes
  the inner expression (numpy rules turn `1/tau` into float64) and casts once with
  `nb.float32(...)`, while Bend computes in float32 throughout.

**Verification ladder** — know which rung you are on, and say so:
1. bit-exact vs a float32 kernel with the same op order (catches transcription);
2. ~1e-4 vs the real `NbHybridBackend` (catches semantics);
3. a *differential* probe — e.g. all ICs = 1.0 and `w[e] = 100*(e+1)`, so each
   row's coupling *is* the list of edges it summed. This is what found the
   one-edge history lag and the tick/slot off-by-one; inspect it by eye.

Trap that nearly faked a result: `cv` is a model **parameter** —
`cr*Coupling_Term_r + cv*Coupling_Term_V` — and `MontbrioPazoRoxin`'s `cv`
default is **0.0**. A job with `cv=1.0` disagrees with the reference by ~20 % and
still looks entirely plausible. Check generated reference source when a
discrepancy is "too big to be rounding but too small to be structural".

---

## 4. The part Bend is genuinely good at: verified configuration

The insight that changes what you can do is that **you can make decidability
return a `Type`**, which turns a decidable predicate into a proposition:

```bend
def le_ok(+a: Nat, +b: Nat) -> Type:   # Unit iff a <= b, Empty otherwise
  match a b:
    case 0n _: Unit
    case 1n+p 0n: Empty
    case 1n+p 1n+q: le_ok(p, q)

def lt_ok(+a: Nat, +b: Nat) -> Type:
  le_ok(Nat.add(a, 1n), b)
```

`le_ok(a, b)` **is** "a ≤ b". Then a general lemma is proved once and
instantiated at any runtime value:

```bend
def le_refl(+x: Nat) -> le_ok(x, x):
  match x:
    case 0n: Unit{}
    case 1n+p: le_refl(p)

def succ_lt(+x: Nat) -> lt_ok(x, Nat.add(x, 1n)):
  le_refl(Nat.add(x, 1n))            # lt_ok(x, x+1) == le_ok(x+1, x+1)
```

**Design rule: put structure in `Nat`, not `U32`.** Index arithmetic, ticks,
`k_j`, horizons and counts are `Nat` at the configuration boundary — where
proving matters and speed does not — and become `U32` only at the leaves of the
hot loop. `Nat` is unary, so never put it in an inner loop.

What this buys on multi-dt, which currently lives in prose comments:

```bend
def newest(+tick: Nat, +p: Nat) -> Nat:      # source steps pushed by `tick`
  Nat.div(Nat.sub(tick, 1n), Nat.add(1n, p))

# The zero-order-hold clamp is NECESSARY, not defensive: a zero-delay edge asks
# for sample div(tick-1,K)+1, strictly newer than anything pushed.
def zoh_is_necessary(+tick: Nat, +p: Nat) ->
    lt_ok(newest(tick, p), Nat.add(newest(tick, p), 1n)):
  succ_lt(newest(tick, p))

# A ring of maxdelay+1+s always covers the deepest delay asked for.
def horizon_covers(+d: Nat, +s: Nat) ->
    le_ok(Nat.add(d, 1n), Nat.add(Nat.add(d, 1n), s)):
  add_mono(Nat.add(d, 1n), s)
```

One lemma each, instantiated at whatever the engine computes. An ill-formed
configuration then becomes a type error: a `Config` constructor that matches on
`le_ok(maxdelay, horizon)` and dies on `Empty`.

**Mandatory: keep a negative test in the same file.** I got `le_ok` wrong twice —
once accepting a false claim, once rejecting a true one — and the only thing that
caught it was a deliberately false law (`x < x`) that must be rejected. A
hand-rolled decider without a negative control is worthless.

**What this cannot do:** prove the drift, the coupling arithmetic, or anything
quantitative. Those need §3's ladder. And because laws are *symmetric* — if you
mistranscribe the same way in the code and in the law, the law passes — laws never
replace differential testing against an independent implementation.

---

## 5. Integration shape: it has to be a binary

Bend emits a native binary, C, JS, `.mjs` or BendTT. There is no Python target
and no way to call a Bend def from Python:

- the emitted C is a whole `int main` with everything `static` — a toy def's name
  appears **zero times** in the output, so there are no symbols to link against;
- the only host-code door is *effects* (`import "./x.c"`), and that is Bend calling
  C, not C calling Bend.

So: a binary, Python as the client, files on the data plane. The cost is
**zero in practice** because crossings are per sweep point, not per step.

Two forced consequences of the ownership model, both easy to get wrong:
- `List<String>` (argv) is single-owner, so you cannot index it repeatedly; get
  paths from `IO.get_env` instead, which returns a copyable `String`.
- each bulk section needs its **own file**, because a decoded `Array` has exactly
  one consumer.

And since floats cannot be bit-reinterpreted (`F32.to_u32` is a numeric
truncation), the job file carries raw u32 words with floats as scaled integers,
and **output must be text**. Use `round(value * 1e6)` integers rather than
`F32.show`, which is not round-trip exact and will manufacture phantom ulp
failures in your comparison harness.

---

## 6. If a GPU port is ever the goal

Read `bend guide shaders` first. The facts that matter: a `!` ships a cube of
16,384 lanes; target 4⁷ leaves, one per lane; ~0.4–0.5 ms per fork iteration;
memory is one heap, with PCIe page faults on CUDA; a `+` value read by every lane
costs an atomic.

The blocker is §1.3: the history ring is a single-owner `Array` and cannot be
shared across a fork. A GPU port would need the **forkable snapshot-list
history** — the representation this prototype rejected because it is ~6× slower
on CPU. So the GPU port is a deliberate reversal of a CPU optimisation, not a
flag flip. Decide that trade once, on purpose; don't discover it later.

Today the honest answer is: 8 sweep points = 8 lanes of 16,384, so the GPU buys
nothing over 8 CPU threads — but real TVB sweeps have 10³–10⁵ points, and that is
the regime the design already fits.

---

## 7. Dead ends — do not repeat these

- **Forking inside a step.** Per-node or per-edge fork-join is 5.7× slower at best
  and ~1000× worse per edge. Measured twice, from opposite directions.
- **`IO.spawn` for pure parallelism.** Serial; it schedules *effects*.
- **Chasing float laws.** Not expressible. The interesting properties are
  structural/combinatorial; go find those instead.
- **Regrouping the model equations for elegance.** It changes rounding and breaks
  bit-parity. Op order is the spec.
- **Assuming `F32` is not `float`.** It is, exactly. That is why the port is
  plausible at all.
- **Copying `nb_hybrid` into Bend file-by-file.** You inherit its data-layout
  assumptions (flat mutable arrays, reusable buffers) that the ownership model
  forbids, and you lose the opportunity to design the verified scaffolding.
- **Trusting a micro-benchmark written in a hurry.** It produced a 15× error in
  one direction and a 4× JIT artifact in another; both would have changed the
  architecture if believed.

---

## 8. Starting a new Bend component in this repo

1. `/home/duke/.bend/bin/bend guide`, then `bend base` — read, don't recall.
2. Build the **numba reference and differential harness first**. You cannot debug
   a simulator against nothing, and the harness is what finds real bugs.
3. Decide representation per layer (§2): `Nat` where you want proofs, `U32`
   where you want speed, `F32` only for dfuns.
4. Measure fork granularity before writing the inner loop (§1.4).
5. Decide integration shape before writing the CLI (§5) — it dictates the job
   format.
6. Write the decider and its negative test together (§4).
7. Check `PROOF.bend --verdict` and the numerical harness both, every time.

Existing example to copy from: `mcore.bend` (model + laws), `mengine.bend`
(loops over single-owner arrays), `montbrio_sweep.bend` (CLI + parallel sweep),
`compare_montbrio.py` (the verification ladder, including the `--disable-delays`
negative control).