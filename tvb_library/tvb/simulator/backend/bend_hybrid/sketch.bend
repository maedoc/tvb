# Illustrative Bend 2.0 sketch for the TVB cpp_hybrid backend.
#
# This file *checks and runs* under the installed compiler:
#   /home/duke/.bend/bin/bend sketch.bend
# It is NOT a working simulator -- it is the smallest faithful core (one MPR
# dfun + Heun + a parallel per-cell step + the ring-buffer push/read) used to
# validate that the translation shape in SKETCH.md is real Bend.  See SKETCH.md
# for the full design (coupling projections, monitors, the dfungen analog).
#
# Key idioms this pins down (Bend 2.0.34), all learned the hard way:
#   * numbers are F32 = IEEE single == C++ float  (no f24, and no F64)
#   * parallelism is a *parallel let* `a b = f(x) g(y)` inside a recursive def;
#     there is no `bend x = e, y = e:` block binding
#   * there is NO `if` syntax -- a Bool is `match`ed on `True{}` / `False{}`
#   * there is no `x.field` syntax -- fields are read by `match` on a parameter
#   * constructors are built positionally: `D{a, b}`, not `D{dr: a, dv_m: b}`
#   * arrays give in-place mutation under purity: `[0 : F32*8n]`, `a[i]`,
#     `a[i] <- v`, indexes wrap around

import Base

# ---------------------------------------------------------------------------
# State as a balanced tree over "unit cells" (node, mode).
#
# The C++ has a flat `float x[(n_svar, n_node, n_modes, W)]`; the `W` SIMD lane
# dimension is dropped (SKETCH.md §3.1) and `n_svar` is carried by the tuple
# shape instead of the stride.  A Cell is one (node, mode) state vector.
#
# Note the accessor defs: Bend has no `x.field`, so every field read is a
# `match` on a parameter.  That is a real porting cost -- in the full backend
# it is paid once per field of `struct proj` and per model parameter, and it is
# the main reason a Bend port wants generated per-model accessor pairs (the
# analog of dfungen.emit_sources) rather than hand-written ones.
# ---------------------------------------------------------------------------

type Cell is Data:
  C{r: F32, v_m: F32}

type Parms is Data:
  P{tau: F32, i_in: F32, delta_p: F32, j_syn: F32, eta: F32}

type DCell is Data:
  D{dr: F32, dv_m: F32}

# the state tree: internal nodes pair two subtrees, leaves are Cells
type State is Data:
  Leaf{+c: Cell}
  Node{l: State, r: State}

def cell_r(c: Cell) -> F32:
  match c:
    case C{+r, v_m}: r

def cell_v_m(c: Cell) -> F32:
  match c:
    case C{r, +v_m}: v_m

def mk_cell(r: F32, v_m: F32) -> Cell:
  C{r, v_m}

def parm_tau(p: Parms) -> F32:
  match p:
    case P{tau, i_in, delta_p, j_syn, eta}: tau

def parm_i_in(p: Parms) -> F32:
  match p:
    case P{tau, i_in, delta_p, j_syn, eta}: i_in

def parm_delta_p(p: Parms) -> F32:
  match p:
    case P{tau, i_in, delta_p, j_syn, eta}: delta_p

def parm_j_syn(p: Parms) -> F32:
  match p:
    case P{tau, i_in, delta_p, j_syn, eta}: j_syn

def parm_eta(p: Parms) -> F32:
  match p:
    case P{tau, i_in, delta_p, j_syn, eta}: eta

def dcell_dr(d: DCell) -> F32:
  match d:
    case D{dr, dV}: dr

def dcell_dv(d: DCell) -> F32:
  match d:
    case D{dr, d_v}: d_v

def mk_dcell(dr: F32, d_v: F32) -> DCell:
  D{dr, d_v}

# ---------------------------------------------------------------------------
# dfun_mpr, term-for-term from _core.cpp's `dfun_mpr<W>` (W dropped):
#
#   r  = r0 * (r0 > 0)
#   dr = (1/tau) * ( delta_p/(PI*tau) + 2*r*V )
#   dV = (1/tau) * ( V^2 + eta + J*tau*r + I + cr*c0 - PI^2*r^2*tau^2 )
#
# `cr` is the single external coupling slot (cvar index 0), matching the C++
# model's `cvar = [0]`; external coupling enters only the membrane potential.
# ---------------------------------------------------------------------------

def dfun_mpr(+c: Cell, +p: Parms, +cr: F32) -> DCell:
  # `+` marks a reusable let; Bend lets are affine by default and every one of
  # these is read more than once below.
  +tau : F32 = parm_tau(p)
  +i_in : F32 = parm_i_in(p)
  +delta_p : F32 = parm_delta_p(p)
  +j_syn : F32 = parm_j_syn(p)
  +eta : F32 = parm_eta(p)
  +r0 : F32 = cell_r(c)
  # C++ `r = r0 * (r0 > 0)` kept as a multiply by the 0/1 mask: same float
  # semantics (a branch would diverge on NaN/inf, a multiply does not).
  # Operators in Bend 2.0 demand an explicit type annotation, so the body is
  # written with the F32 verbs -- exactly the `-ffp-contract=off` discipline the
  # C++ core follows, one call per operator, no fused reassociation.
  +r : F32 = F32.mul(r0, U32.to_f32(Bool.to_u32(F32.is_gt(r0, 0.0))))
  +v_m : F32 = cell_v_m(c)
  v2 = F32.mul(v_m, v_m)
  tau2 = F32.mul(tau, tau)
  dr = F32.div(
    F32.add(F32.div(delta_p, F32.mul(F32.pi(), tau)),
            F32.mul(F32.mul(2.0, r), v_m)), tau)
  dV = F32.div(
    F32.sub(
      F32.add(F32.add(F32.add(F32.add(v2, eta), F32.mul(F32.mul(j_syn, tau), r)),
                      i_in), cr),
      F32.mul(F32.mul(F32.mul(F32.mul(F32.pi(), F32.pi()), r), r), tau2)),
    tau)
  D{dr, dV}

# ---------------------------------------------------------------------------
# Heun with pure recomputation.
#
# The C++ needs three scratch buffers (dx, xi, dxi) only because it reuses
# memory across the two stages.  Bend needs none: both dfun evaluations are
# independent pure calls.  This is the single biggest structural
# simplification of the port.
#
# Coupling stays fixed across the two stages -- in C++ because `c` is computed
# once per master step, and here because `cr` is a parameter, not a recompute.
# ---------------------------------------------------------------------------

def axpy(+c: Cell, +d: DCell, +a: F32) -> Cell:
  C{F32.add(cell_r(c), F32.mul(a, dcell_dr(d))),
   F32.add(cell_v_m(c), F32.mul(a, dcell_dv(d)))}

def clamp_mpr(+c: Cell) -> Cell:
  # clamp_dispatch for MPR: r = r * (r > 0)
  +r : F32 = cell_r(c)
  C{F32.mul(r, U32.to_f32(Bool.to_u32(F32.is_gt(r, 0.0)))), cell_v_m(c)}

def heun_cell(+c: Cell, +p: Parms, +cr: F32, +dt: F32) -> Cell:
  +d1 : DCell = dfun_mpr(c, p, cr)
  xi = clamp_mpr(axpy(c, d1, dt))
  +d2 : DCell = dfun_mpr(xi, p, cr)
  m = mk_dcell(F32.mul(0.5, F32.add(dcell_dr(d1), dcell_dr(d2))),
               F32.mul(0.5, F32.add(dcell_dv(d1), dcell_dv(d2))))
  clamp_mpr(axpy(c, m, dt))

def euler_cell(+c: Cell, +p: Parms, +cr: F32, +dt: F32) -> Cell:
  clamp_mpr(axpy(c, dfun_mpr(c, p, cr), dt))

# ---------------------------------------------------------------------------
# One subnet step, parallel over every (node, mode) cell.
#
# Bend 2.0 parallelism is the parallel let: `a b = f(x) g(y)`.  The recursion
# runs over the tree spine, so the two halves of a split are structurally
# identical (equal sizes) and the fork/join stays balanced -- which is what the
# contention-free scheduler needs to keep every core busy.
# ---------------------------------------------------------------------------

def step_leaf(+c: Cell, +p: Parms, +cr: F32, +dt: F32, +heun: Bool) -> State:
  # the C++ `if (heun)` becomes a match on the Bool payload
  match heun:
    case True{}:
      Leaf{heun_cell(c, p, cr, dt)}
    case False{}:
      Leaf{euler_cell(c, p, cr, dt)}

def step_tree(s: State, +p: Parms, +cr: F32, +dt: F32, +heun: Bool) -> State:
  match s:
    case Leaf{+c}:
      step_leaf(c, p, cr, dt, heun)
    case Node{l, r}:
      nl nr = step_tree(l, p, cr, dt, heun) step_tree(r, p, cr, dt, heun)
      Node{nl, nr}

def cell_of(s: State) -> Cell:
  match s:
    case Leaf{+c}:
      c
    case Node{l, r}:
      c0 = cell_of(l)
      c1 = cell_of(r)
      c0

# ---------------------------------------------------------------------------
# The history ring.
#
# C++ keeps `buf[(n_svar, n_node, n_modes, H, W)]` with `push_state` writing
# slot `t & (H-1)` and coupling reading slot `t-1-delay`.  In Bend this is an
# Array with wrapping indexes -- `Array.set` at `t & (H-1)` is the exact
# translation.  (The first draft of this sketch proposed a cons list and an
# O(delay) ancestor walk; Array is strictly better and was found by reading
# `bend base`.)  `Array<Cell>` is used directly so one slot holds a whole cell.
# ---------------------------------------------------------------------------

def ring_new(depth: Nat, v: Cell) -> Array<Cell>:
  Array.new(Cell, depth, v)

def push_state(hist: Array<Cell>, t: U32, cell: Cell) -> Array<Cell>:
  # An Array is a Type, not Data: it has exactly one owner and cannot be copied,
  # so `hist` stays affine and the written array is handed back (which is exactly
  # `a[i] <- v` under the hood).  H = 8 here; the H-1 mask is `7` because the
  # depth is a power of two, the
  # same assumption the C++ ring makes.
  Array.set(Cell, hist, U32.and(t, 7), cell)

def read_cell(p: Array<Cell> & Cell) -> Cell:
  # Array.get hands the array back next to the element (a dependent pair).  A
  # match must scrutinize a parameter, never a computed value or a local
  # binder -- hence this one-line helper.
  match p:
    case (hist, +c):
      c

def read_state(hist: Array<Cell>, t: U32) -> Cell:
  read_cell(Array.get(Cell, hist, U32.and(t, 7)))

# ---------------------------------------------------------------------------
# Smoke test: Heun steps of the uniform MPR fixed point.
#
# With I = 30 pA and delta_p = 2*PI*tau the standard bistable equilibrium sits at
# r ~ 1 Hz, V ~ -70 mV, where dfun_mpr is zero -- so a correct translation must
# leave it fixed to within float32 round-off.  Any transcription error in the
# equations shows up immediately as drift, which is exactly the sanity check a
# sketch should give.  The real check is `test_cpp_hybrid_parity.py`.
# ---------------------------------------------------------------------------

def main() -> IO(Unit):
  # Bend's affine discipline: a `let` may be used at most once, so anything read
  # twice (the equilibrium cell, the params) is bound `+`, which is allowed only
  # because those datatypes are `is Data`.  Float literals need an expected type
  # from context (`+x : F32 = ...`); a bare `a = 1.0` will not infer.
  +tau : F32 = 10.0
  +p : Parms = P{tau, 30.0, F32.mul(2.0, F32.mul(F32.pi(), tau)), 0.4, F32.neg(1.0)}
  # the fixed point of this exact dfun (solved from dr = dV = 0): the sketch
  # params are the *normalised* MPR ones (tau=10 ms, Delta=2*PI*tau, J=0.4,
  # I=30 pA, eta=-1), not TVB's a/b/c/d variant -- the point is that a correct
  # translation leaves this state fixed to float32 round-off.
  +eq : Cell = C{0.2261181, F32.neg(4.4224676)}
  +c1 : Cell = heun_cell(eq, p, 0.0, 0.01)
  +c2 : Cell = heun_cell(c1, p, 0.0, 0.01)
  hist = ring_new(3n, eq)
  h2 = push_state(hist, 0, c1)
  h3 = push_state(h2, 1, c2)
  # a read hands the array back beside the element; the array is affine, so the
  # helper keeps only the cell and lets the array fall
  # An Array is a single-owner Type, so it cannot be cloned or read twice: build
  # a second identical ring to inspect a second slot.
  hist_b = ring_new(3n, eq)
  h2b = push_state(hist_b, 0, c1)
  h3b = push_state(h2b, 1, c2)
  +back : Cell = read_state(h3, 0)
  +slot1 : Cell = read_state(h3b, 1)

  # a 4-cell tree stepped in parallel must give the same per-cell answers
  +s0 : State = Node{Node{Leaf{eq}, Leaf{eq}}, Node{Leaf{eq}, Leaf{eq}}}
  +s1 : State = step_tree(s0, p, 0.0, 0.01, True{})
  +s2 : State = step_tree(s1, p, 0.0, 0.01, True{})
  +tl : Cell = cell_of(s2)

  # several IO steps must live in a `do IO<Unit>` block; a bare sequence of
  # IO.print statements is a parse error.
  do IO<Unit>:
    IO.print("r0      = " ++ F32.show(cell_r(eq)))
    IO.print("r1      = " ++ F32.show(cell_r(c1)))
    IO.print("r2      = " ++ F32.show(cell_r(c2)))
    IO.print("ring[0] = " ++ F32.show(cell_r(back)))
    IO.print("ring[1] = " ++ F32.show(cell_r(slot1)))
    IO.print("tree    = " ++ F32.show(cell_r(tl)))
