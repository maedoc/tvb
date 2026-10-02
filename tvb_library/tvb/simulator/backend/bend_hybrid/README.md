# Bend MontbrioPazoRoxin hybrid prototype

A minimal, idiomatic Bend port of the numba hybrid kernel
(`tvb/simulator/backend/nb_hybrid.py`) for one subnet, one mode, MontbrioPazoRoxin,
Heun, a CSR connectome with per-edge integer-step delays, and a parameter sweep
over the projection coupling scale.

It ships as a **standalone binary**, not a Python extension — see *Runtime shape*
below for why Bend 2.0 cannot be one.

| file | role |
|---|---|
| `mcore.bend` | the model: decoding, the Montbrio drift, the clamp, one Heun step |
| `mengine.bend` | the simulation: coupling pass with delays, state update, history push, the step loop |
| `montbrio_sweep.bend` | the CLI: job loading, the data-parallel sweep, output |
| `LAWS.bend` / `PROOF.bend` | the specification and its proofs (`bend PROOF.bend --verdict`) |
| `run_montbrio.py` | writes the job files, runs the binary, parses the output |
| `compare_montbrio.py` | compares against numba and `NbHybridBackend`; parity, isolation |
| `bench_montbrio.py` | the benchmark |
| `BEND_TVB_GUIDE.md` | **start here for new work**: which parts of a TVB hybrid sim suit Bend, and why |
| `NOTES.md` | syntax and toolchain traps; measured runtime facts |
| `README.md` | this file — design, results, and limits |

```bash
BEND=/home/duke/.bend/bin/bend
$BEND montbrio_sweep.bend -o montbrio_sweep        # build (~3 s)

python run_montbrio.py    --n 300 --steps 300 --points 8 --threads 8
python compare_montbrio.py --n 300 --steps 300 --points 8 --threads 8
python bench_montbrio.py  --n 300 --steps 300 --points 8 --threads 8
$BEND PROOF.bend --verdict                          # ALL PROOFS CHECK
```

---

## 1. Measured results

Machine: 8 cores, no CUDA. `tvb_library/.venv` (numba 0.68, numpy 2.5).
Workload: `N=300` nodes, dense off-diagonal connectome (89 700 directed edges),
per-edge delays `0..10` steps, ring of 16 slots, 300 steps, 8 sweep points over
`coupling_scale ∈ [0, 5]`.

### Numerics

| check | result |
|---|---|
| one-step drift, bit-exact vs a float32 numba kernel | **exact** (`r` and `V`), with and without delays |
| traces vs `NbHybridBackend`, delays 0..10, **coupled** (scale 2.0) | max rel dev `r` **9.2e-06**, `V` **5.6e-07** (tol 1e-4) |
| traces vs `NbHybridBackend`, delays 0..10, uncoupled (scale 0) | max rel dev `r` **0.0**, `V` **5.1e-07** |
| traces vs `NbHybridBackend`, zero delays, coupled | max rel dev `r` **0.0**, `V` **5.6e-07** |
| identical steps (per-step integers) | coupled+delays: `r` 299/300, `V` 292/300 — uncoupled: `r` 300/300 |
| delays zeroed in Bend only (must fail) | **fails**: 1.2e-02 (`r`), 1.4e-02 (`V`), identical steps 218/300 |
| each sweep point alone vs in-sweep | **exact**, deviation 0 |
| repeated runs | byte-identical |

Note the coupling matters to the headline: an uncoupled run (`scale = 0`) has
`r` bitwise equal to `nb_hybrid` for all 300 steps, but it does not exercise the
delayed gather at all, so the **coupled** row is the one that means anything.
`r` is otherwise within 1e-5 and `V` within 6e-07 of the reference; both gaps
are the float64-intermediate term of §3.

### Speed

| | 8-point sweep | per point |
|---|---|---|
| **Bend** (1 process, 8 threads) | **553.8 ms** | 69.2 ms |
| numba (8 points, sequential) | 2821.2 ms | 352.6 ms |
| Bend, single point, 1 thread | — | 331.2 ms |
| numba, single point | — | 344.7 ms |

Sweep: **5.09× faster** than the numba baseline. Per point on one core Bend is
**0.96×** numba — the kernel is marginally slower, and the sweep win comes
entirely from the 8-way fan-out (331 → 69 ms per point, 4.8× on 8 cores).
min of 5 reps after 2 warmups; medians 576 ms / 2830 ms.

The numba baseline is the one in `bench_cpp_vs_numba.py`: eight points driven
one at a time. Both sides pay per-point array/buffer setup.

---

## 2. Bend 2.0 idioms the design depends on

Every item here was established by running the compiler; the ones that cost the
most time are the ones that differ from what you would write in any other
language.

**Numeric types.** `F32` is IEEE-754 single precision, bit-identical to C++
`float` — verified in `base.bend` (`type F32 is Data: F32{data: Word(32n)}`).
There is no `f24` (that was the old HigherOrderCO Bend) and **no `F64`** at
all. `F32.to_u32` is a numeric truncation, not a bit cast, so Bend can neither
read nor write a float32 buffer. That single fact dictates the whole data plane.

**No `if`.** A condition is a `match` on `True{}` / `False{}`, or
`Bool.pick(T, c, a, b)` — which consumes *both* branches, so a value used in
either is consumed twice.

**No field access.** `x.f` does not exist. Every field read is its own accessor
def that matches on the parameter. For `struct proj`-shaped data this is a real
per-field tax, and it is the reason a Bend port wants generated per-model code
rather than hand-written kernels.

**Affine by default.** A `let` or parameter may be used at most once; `+` marks a
binder reusable, which requires its type to be `Data`. An `Array` is a `Type`
(single owner) and can never be `+` — it must be threaded. A record holding
arrays is therefore `is Type` too.

**Termination checking.** A recursive call needs a *shrinking* argument, read
left to right, and everything after it is free. A counted loop grows its index,
so each loop threads a remaining count first and the absolute index alongside.
A `match` supplies the smaller value directly (`case 1n+p` → recurse on `p`),
which is why the loops look the way they do.

**`match` inspects parameters and pattern bindings only** — never a computed
value, and never a local binder. So a fetched value has to be carried in as a
*parameter* to be destructured, which forces a one-step lag between fetching and
using. This is the single deepest constraint in the port; §4 is about it.

**One `match` per def, several values at once with `match a b:`** in binder
order. A `let` may not precede a `match` on a parameter.

**No mutual recursion.** Two functions that call each other become one def with
an argument selecting which to run. Where mutual recursion seemed unavoidable
(the `emit_both` / `in_sec` pair, the argv parsing), the fix was a flat
multi-cons pattern (`case b0 <> b1 <> b2 <> b3 <> t:`) or `Maybe.default`.

**Arrays** give in-place mutation under purity: `Array.new(T, d, v)` with a
power-of-two size and **wrapping indexes**, `Array.set(T, a, i, v)`,
`Array.get(T, a, i)` returning a dependent pair `Array<T> & T`, `Array.to_list`.
`Array.get` needs the element type spelled out and the type cannot be inferred
from the destination.

**Parallelism is the parallel let** `a b = f(x) g(x)` — there is no
`bend x = e:` block binding. **`IO.spawn` does not fan pure work out**: on this workload (300 nodes, 300
steps, delays) the spawn version measured 1 point 206 ms, 2 points 432 ms, 8
points 1412 ms — exactly serial, `n * t`. That is why the sweep was rewritten
with parallel lets (the spawn code path no longer exists in `montbrio_sweep.bend`). The
whole parallel win in §1 comes from nested parallel lets inside one `do` block.

**Laws.** `{==}` is *structural* reflexivity — both sides must reduce to the
same term. Integer arithmetic normalises; **float values do not**, not even
`F32.add(0.0, 0.0) == 0.0`, nor a `match` on a concrete `Bool`. So Bend 2.0
cannot prove a float value equality at all, and this prototype's laws are
structural identities plus integer identities; every numeric claim is checked
numerically by `compare_montbrio.py` instead.

---

## 3. Where the numbers can diverge from numba, and how they are pinned

The drift is a **literal transcription** of the model's expression strings in
`models/infinite_theta.py`:

```
"r": "1/tau * ( Delta / (pi * tau) + 2 * V * r)"
"V": "1/tau * ( V*V - pi*pi*tau*tau*r*r + eta + J * tau * r + I
                + cr * Coupling_Term_r + cv * Coupling_Term_V )"
```

evaluated strictly left to right, one rounding per operator, because the numba
kernel embeds the same string and therefore performs the same operations in the
same association. An algebraically equivalent regrouping is **not**
bit-identical: `(1/tau) * X` and `X / tau` round differently, and
`((((pi*pi)*tau)*tau)*r)*r` is not the same term as `(pi*tau)*(pi*tau)*(r*r)`.
`LAWS.bend` pins this: mistranscribing `2*V*r` as `2*r*V` makes
`bend PROOF.bend` report `SOME PROOFS FAIL` (IEEE multiplication is commutative,
so the *values* still agree — the law exists to stop a future edit silently
regrouping a sum, which would change rounding).

Remaining, deliberate sources of divergence:

1. **float32 vs float64 intermediates.** `nb_hybrid`'s generated kernel embeds
   `pi = np.pi` and reads model parameters as Python floats, so parts of its
   drift evaluate in **float64** and round once on the way back into the float32
   state. Bend has no `F64` and computes in float32 throughout. This is the
   dominant term in the residual 7e-08, and it is why the traces are not bitwise
   equal even though the one-step drift against a *float32* kernel is.
2. **`cr` / `cv` are parameters, not the coupling.** The coupling term is
   `cr*Coupling_Term_r + cv*Coupling_Term_V` — the model weight times the
   incoming value. Getting this wrong is silent: the run still looks plausible.
   It is the default `cv = 0.0` (coupling enters through the rate variable
   only), and a job with `cv = 1.0` disagrees with the reference by ~20 %.
3. **The fixed-point job encoding.** Bend reads scaled integers and divides by
   1e6 in `F32`. The reference therefore receives the *same* decoded values, not
   the original ones — otherwise the comparison would measure the encoding
   rather than the arithmetic.
4. **`F32.show` is not round-trip exact** (it prints ~7 significant digits), so a
   text float can land an ulp from the value actually computed. The trace
   channel therefore carries `round(value * 1e6)` as an **integer**, which makes
   the comparison exact; this was masking a spurious "1 ulp" difference before
   it was found.

---

## 4. Three bugs worth recording

They are the reason the delay handling works at all, and each was found by a
measurement rather than by reading the code.

**The history read lagged one edge.** `Array.get` returns a dependent pair, and a
`match` may only inspect a parameter — so a fetched value has to be carried into
the *next* call as a pair. That made every iteration consume the previous edge's
address. The fix was a two-step prefetch: carry the packed edge word for edge
`e+1` as well, so the current call can form edge `e+1`'s address and fetch its
value for the next call. Each array is still used exactly once per iteration.
Verification trick: set every initial state and weight to 1.0 and give edge `e`
the weight `100*(e+1)` — then each row's coupling *is* the list of edges it
summed.

**The seed address hard-coded tick 1.** `seed_coup` formed the address of the
first edge's read with `t = 1` written into the expression, so from step 2 on
the *first* row read the wrong history slot while every other row was correct.

**The tick advanced in the wrong pass.** The `t` increment lived in the coupling
pass, but the update pass reads `t` to derive the trace index (`t-1`) and the
push slot (`t`) — so from step 2 on both were off by one.

---

## 5. Runtime shape: why a binary and not a Python extension

Bend 2.0 emits a native binary, C, JS, `.mjs` or BendTT. There is no Python
target and no way to call a Bend def from Python:

* the emitted C is a **whole program** — `int main(argc, argv)` plus everything
  else `static`. A toy def's name appears **zero times** in the emitted C; it is
  inlined into `main`. There are no exported symbols to link against, so a
  hand-written nanobind/pybind11 layer is impossible without patching the
  compiler's emitter;
* the only host-code door is *effects* (`import "./x.c"`), and that is Bend
  calling C, not C calling Bend.

So the CLI is a binary and Python is the client. The data plane is binary files
holding little-endian u32 words (`File.read_bytes` returns one `U32` per byte),
which the job needs anyway because Bend cannot emit float32 bytes. The control
plane is argv (`IO.args` → `U32.read`) plus environment variables for the eight
section paths — a `List<String>` is a single-owner `Type` and cannot be copied
for repeated indexing, while `IO.get_env` hands back a `String`, which is
`Data`. Each section lives in its **own file** so that each decoded `Array` has
exactly one consumer, for the same single-owner reason.

---

## 6. What this prototype does NOT cover

Stated explicitly, because every item is a real difference from
`nb_hybrid`/`cpp_hybrid` and none of them is a rounding detail.

1. **One subnet, one mode.** No inter-projection, no mode maps, no multi-area
   state.
2. **One model.** MontbrioPazoRoxin only, with a hand-transcribed drift. No
   generic `state_variable_dfuns` codegen — the analogue of `dfungen.py` does
   not exist yet, so the other 26 models `nb_hybrid` supports are absent.
3. **Integer-step delays only.** The multi-dt fractional interpolation
   (`tau = (t-1)/K - delay`, `s0/s1`, `alpha`) is not implemented: there is no
   `K`, one `dt` for everything.
4. **Coupling functions.** `Linear` only (`a*x + b`). The other seven classes
   (`scaling`, `sigmoidal`, `sigmoidal_jr`, `sigmoidal_jr_legacy`, `tanh`,
   `difference`, `kuramoto`, `pre_sigmoidal`, `pre_sigmoidal_dynamic`) and their
   `globalT` pre-pass are absent.
5. **Monitors.** No Raw/Subsample/Bold monitor engines. The prototype emits
   node 0's `r` and `V` at every step as a fixed-point trace, which is enough to
   check parity but is not a monitor: no temporal average, no HRF convolution,
   no chunk normalisation, no sensors.
6. **No noise, no stimulus, no surface.** Deterministic Heun only.
7. **Sweep fan-out is fixed at 8 lanes.** `sweep8` always forks 8 branches and
   masks the lanes past `n_sweep`; a 3-point sweep wastes 5 branches, and a
   16-point sweep is wrong. A recursive fan-out would be better; this was a
   deliberate choice to keep the loop shape simple.
8. **Floating-point output only for node 0.** The trace is one node's two
   series. Spatial sums and full-state output are not implemented.
9. **No laws for the numerics.** Bend 2.0 cannot prove a float value equality,
   so the numerical claims live in `compare_montbrio.py`, not in `PROOF.bend`.
   `--verdict` gates the structural and integer laws only.
10. **Performance is CPU only.** No CUDA on this machine, so `!` calls fall back
    to CPU. The GPU path (`--gpu`, the `file.gpu` sidecar) is untested, and the
    fork-join scheduler's GPU behaviour is unknown here.
11. **No integration with the TVB build.** `bend_hybrid/` is inert: it is not
    wired into `tvb_library/CMakeLists.txt`, imports nothing from TVB, and no
    `BendHybridBackend` is registered. `compare_montbrio.py` builds the network
    by hand rather than going through `NetworkSet`.
12. **Stability is not a constraint.** `state_variable_boundaries` is honoured
    for `r` only (`r < 0 → 0`); the upper bound and the `isfinite` guard the
    generated kernel emits are not.
