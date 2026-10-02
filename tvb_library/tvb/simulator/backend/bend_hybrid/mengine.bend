# Simulation engine: CSR connectome with per-edge integer-step delays, Heun
# integrator, parameter sweep over the projection coupling scale.  Pure (no IO).
import ./mcore.bend as Core

# --------------------------------------------------------------------------
# Bend idioms this engine depends on (verified against bend 2.0.34)
#
#  * A value RETURNED by a call cannot be destructured by the caller -- `match`
#    only inspects parameters or pattern bindings, never computed values.  So
#    every loop threads its whole state through ONE record and returns that
#    record; the caller passes it straight on as a parameter.
#  * Bend's termination checker reads a recursive call's arguments left to
#    right and wants a SHRINKING argument first; everything after it is free.
#    So each loop leads with a fuel counter that the match pattern supplies
#    (`case 1n+f` -> `f`), and carries everything else in the record.
#  * `Array.get` returns a dependent pair `Array<T> & T`, so a fetched element
#    is threaded as an ARGUMENT and matched on the next call.  The record is
#    rebuilt from the matched components, each consumed exactly once.
#  * an Array is a single-owner `Type`: never marked `+`, always threaded.
#  * `Array.set` needs the element type spelled out, and an unconditional
#    branch would duplicate the whole record, so a conditional write goes
#    through `maybe_set`, which matches on the Bool and returns the array.
# --------------------------------------------------------------------------

# The whole per-sweep-point simulation state.  Both the coupling loop and the
# update loop thread this one record and return it, because a value returned by
# a call cannot be destructured -- it has to be passed straight on as a
# parameter.  `Sim` therefore also carries the fields a given loop does not
# touch, so a loop can hand the record on untouched.
#
# The edge/tgt arrays carry ONE SENTINEL EDGE past the end (target node
# n_nodes, weight 0, delay 0).  It makes the flat coupling loop flush the final
# row exactly like any other, which removes the need for a separate final-flush
# pass and its extra thread of the arrays.
type Sim is Type:
  Sim{edge: Array<U32>,   # per-edge idx (low 16) | delay (high 16)
     tgt: Array<U32>,    # target node of the edge (CSR rows, sorted)
     w: Array<F32>,      # per-edge weight
     hr: Array<F32>,     # history of r, addressed node*hslots + slot
     hv: Array<F32>,     # history of v
     r: Array<F32>,      # current state r
     v: Array<F32>,      # current state V
     cr: Array<F32>,     # coupling into r this step
     cv: Array<F32>,     # coupling into V this step
     tr: Array<F32>,     # monitor trace, 2*(t-1) = r of node 0, +1 = V
     t: U32,             # 1-based master tick
     nnz: U32,           # number of real edges (excluding the sentinel)
     n_nodes: U32,
     hslots: U32,        # ring size (power of two), slot = t & (hslots-1)
     tmask: U32,
     cfa: F32,           # Linear cfun a
     cfb: F32,           # Linear cfun b
     scale: F32,         # projection coupling scale (the swept parameter)
     c: Core.Cfg}



# per-step constants; `t` is the 1-based master tick
type Ctx is Data:
  X{t: U32, hslots: U32, tmask: U32, cfa: F32, cfb: F32, scale: F32}

# accessors ----------------------------------------------------------------

def x_t(x: Ctx) -> U32:
  match x:
    case X{t, hslots, tmask, cfa, cfb, scale}: t

def x_hslots(x: Ctx) -> U32:
  match x:
    case X{t, hslots, tmask, cfa, cfb, scale}: hslots

def x_tmask(x: Ctx) -> U32:
  match x:
    case X{t, hslots, tmask, cfa, cfb, scale}: tmask

def x_cfa(x: Ctx) -> F32:
  match x:
    case X{t, hslots, tmask, cfa, cfb, scale}: cfa

def x_cfb(x: Ctx) -> F32:
  match x:
    case X{t, hslots, tmask, cfa, cfb, scale}: cfb

def x_scale(x: Ctx) -> F32:
  match x:
    case X{t, hslots, tmask, cfa, cfb, scale}: scale

# --------------------------------------------------------------------------
# per-edge packing and the delayed read address
#
# idelay is in steps and was rounded by the reference implementation
# (hybrid/base_projection.py):
#     idelays = round(lengths.data / cv / dt)
# --------------------------------------------------------------------------

def e_idx(+packed: U32) -> U32:
  U32.and(packed, 65535)

def e_delay(+packed: U32) -> U32:
  U32.shrn(packed, 16n)

def e_slot(+packed: U32, +t: U32, +tmask: U32) -> U32:
  # nb_hybrid single-dt read: slot = (t - 1 - idelay) mod H, with t 1-based.
  # H is a power of two here, so the modulo is a mask.
  U32.and(U32.sub(t, U32.add(1, e_delay(packed))), tmask)

def e_addr(+packed: U32, +t: U32, +hslots: U32, +tmask: U32) -> U32:
  U32.add(U32.mul(e_idx(packed), hslots), e_slot(packed, t, tmask))

def post_cfun(+acc: F32, +x: Ctx) -> F32:
  # Linear cfun post: wsum = a*wsum + b, then wsum *= scale (ts == 1)
  F32.mul(F32.add(F32.mul(x_cfa(x), acc), x_cfb(x)), x_scale(x))

# Bool.pick consumes BOTH branches, so a value used in two branches would be
# consumed twice.  Selecting through a def keeps each operand used once.
def pick_or(+fresh: F32, +acc: F32, +reset: Bool) -> F32:
  match reset:
    case True{}:
      fresh
    case False{}:
      F32.add(acc, fresh)

def maybe_set(a: Array<F32>, +i: U32, +val: F32, +do_it: Bool) -> Array<F32>:
  match do_it:
    case True{}:
      Array.set(F32, a, i, val)
    case False{}:
      a

# --------------------------------------------------------------------------
# Coupling pass, as ONE flat loop over the edges.
#
# The edges arrive in CSR order, i.e. sorted by target node, so the loop can
# carry the per-node accumulator in a register and flush it to cr[j]/cv[j] on
# the first edge of the next row.  That costs one indexed write per NODE; a
# nested per-node/per-edge loop would cost a read-modify-write per EDGE, and in
# Bend it could not be written at all (fusing the inner result back into the
# outer loop's threaded arrays is mutual recursion, which Bend forbids).
# --------------------------------------------------------------------------

# One coupling pass over the CSR edges.

# `pw`/`pt` are the weight and target of edge e; `pep` is the packed edge word
# of edge e+1; `phr`/`phv` carry the state values that edge e reads.

# The two-step prefetch of the packed edge word is not an optimisation, it is
# what makes the read correct.  A fetched value arrives inside a dependent pair,
# and a `match` may only inspect a parameter -- so a value cannot be read and
# used in the same call unless it is carried in as a pair, which means it was
# fetched by the PREVIOUS call.  Fetching it there needs that call to know this
# edge's address, which needs this edge's packed word: hence `pep`.  Each array
# is still used exactly once per call (the one `Array.get` that produces the
# pair for the next call), so the affine discipline holds.
# """
def coup_flat(+fuel: Nat, +e: U32, +j: U32, +accr: F32, +accv: F32,
              pw: (Array<F32> & F32), pt: (Array<U32> & U32),
              pep: (Array<U32> & U32),
              phr: (Array<F32> & F32), phv: (Array<F32> & F32),
              cra: Array<F32>, cva: Array<F32>,
              ra: Array<F32>, va: Array<F32>, tra: Array<F32>,
              +nnz: U32, +n_nodes: U32, +c: Core.Cfg, +x: Ctx) -> Sim:
  match fuel:
    case 0n:
      match pw:
        case (wa, w_val):
          match pt:
            case (ta, t_val):
              match pep:
                case (epa, ep_val):
                  match phr:
                    case (hra, hr_val):
                      match phv:
                        case (hva, hv_val):
                          Sim{epa, ta, wa, hra, hva, ra, va, cra, cva, tra,
                              x_t(x), nnz, n_nodes, x_hslots(x), x_tmask(x),
                              x_cfa(x), x_cfb(x), x_scale(x), c}
    case 1n+f:
      match pw:
        case (w1, +we):
          match pt:
            case (tgt1, +jv):
              match pep:
                case (edge1, +packed2):
                  match phr:
                    case (hr1, +hrv):
                      match phv:
                        case (hv1, +hvv):
                          +addr2 : U32 = e_addr(packed2, x_t(x), x_hslots(x),
                                                 x_tmask(x))
                          +new_row : Bool = U32.is_ne(jv, j)
                          +ne : U32 = U32.add(e, 1)
                          coup_flat(f, ne, jv,
                                    pick_or(F32.mul(we, hrv), accr, new_row),
                                    pick_or(F32.mul(we, hvv), accv, new_row),
                                    Array.get(F32, w1, ne),
                                    Array.get(U32, tgt1, ne),
                                    # the NEXT call prefetches edge e+2, not
                                    # edge e+1: `pep` there yields that call's
                                    # own address, which belongs to edge e+2
                                    Array.get(U32, edge1, U32.add(ne, 1)),
                                    Array.get(F32, hr1, addr2),
                                    Array.get(F32, hv1, addr2),
                                    maybe_set(cra, j, post_cfun(accr, x), new_row),
                                    maybe_set(cva, j, post_cfun(accv, x), new_row),
                                    ra, va, tra, nnz, n_nodes, c, x)

# --------------------------------------------------------------------------
# State-update pass, FUSED with the history push and the monitor trace.
#
# Writing the new state into the ring inside this loop is safe: the coupling for
# step t is already complete for every node, and the next step only reads slots
# <= t-1 while this loop writes slot t.
#
# The trace records node 0's r and V at 2*(t-1) and 2*(t-1)+1.
# --------------------------------------------------------------------------

def write_trace(tr: Array<F32>, +r: F32, +v: F32, +i: U32, +step: U32) -> Array<F32>:
  tr2 = maybe_set(tr, U32.mul(step, 2), r, U32.is_zero(i))
  maybe_set(tr2, U32.add(U32.mul(step, 2), 1), v, U32.is_zero(i))

def upd_flat(+fuel: Nat, +i: U32, +step: U32, +slot: U32,
             pr: (Array<F32> & F32), pv: (Array<F32> & F32),
             pcr: (Array<F32> & F32), pcv: (Array<F32> & F32),
             phr: (Array<F32> & F32), phv: (Array<F32> & F32),
             tra: Array<F32>,
             ea: Array<U32>, ta: Array<U32>, wa: Array<F32>,
             +nnz: U32, +n_nodes: U32, +hslots: U32, +tmask: U32,
             +c: Core.Cfg, +x: Ctx) -> Sim:
  match fuel:
    case 0n:
      match pr:
        case (ra, r_val):
          match pv:
            case (va, v_val):
              match pcr:
                case (cra2, cr_val):
                  match pcv:
                    case (cva2, cv_val):
                      match phr:
                        case (hra, hr_val):
                          match phv:
                            case (hva, hv_val):
                              # the tick advances here: coupling for tick t has
                              # been computed, so the next pass is tick t+1
                              Sim{ea, ta, wa, hra, hva, ra, va, cra2, cva2, tra,
                                  U32.add(x_t(x), 1), nnz, n_nodes, hslots, tmask,
                                  x_cfa(x), x_cfb(x), x_scale(x), c}
    case 1n+f:
      match pr:
        case (r1, x_r):
          match pv:
            case (v1, x_v):
              match pcr:
                case (cr1, c_r):
                  match pcv:
                    case (cv1, c_v):
                      match phr:
                        case (hr1, hr_val):
                          match phv:
                            case (hv1, hv_val):
                              +ni : U32 = U32.add(i, 1)
                              +cell : Core.RV = Core.heun_cell(x_r, x_v, c, c_r, c_v)
                              +nr : F32 = Core.rv_r(cell)
                              +nv : F32 = Core.rv_v(cell)
                              +haddr : U32 = U32.add(U32.mul(i, hslots), slot)
                              upd_flat(f, ni, step, slot,
                                       Array.get(F32, Array.set(F32, r1, i, nr), ni),
                                       Array.get(F32, Array.set(F32, v1, i, nv), ni),
                                       Array.get(F32, cr1, ni),
                                       Array.get(F32, cv1, ni),
                                       Array.get(F32, Array.set(F32, hr1, haddr, nr), i),
                                       Array.get(F32, Array.set(F32, hv1, haddr, nv), i),
                                       write_trace(tra, nr, nv, i, step),
                                       ea, ta, wa,
                                       nnz, n_nodes, hslots, tmask, c, x)

# --------------------------------------------------------------------------
# Bridges between the master step loop and the two flat passes.
#
# A value returned by a call cannot be destructured, so each bridge takes the
# Sim as a PARAMETER (matchable), pulls its arrays out, and seeds the flat
# passes with the `Array.get` pairs they need.
#
# `addr0` is the history address of the FIRST edge.  It is supplied by the
# caller because reading it here would mean destructuring a freshly computed
# pair, which Bend does not allow; the step loop derives it from the first
# edge's idx and delay, which are constants of the job.
# --------------------------------------------------------------------------

def seed_coup(+fuel: Nat, sim: Sim, +idx0: U32, +del0: U32) -> Sim:
  match sim:
    case Sim{edge, tgt, w, hr, hv, r, v, cr, cv, tr, +t, nnz, +n_nodes,
             +hslots, +tmask, cfa, cfb, scale, c}:
      # j starts at 0: CSR rows are ordered and Python guarantees node 0 has
      # at least one edge, so tgt[0] == 0 and the first row does not flush.
      # edge 0's own delayed address for THIS tick: the seed value is fetched
      # by the caller, so the address has to be formed here -- and it depends on
      # the tick, not on a hardcoded 1
      +addr0 : U32 = U32.add(U32.mul(idx0, hslots),
                             U32.and(U32.sub(U32.sub(t, 1), del0), tmask))
      # edge 0's weight/target, edge 1's packed word (the prefetch), and the
      # values edge 0 reads at its own delayed address
      coup_flat(fuel, 0, 0, 0.0, 0.0,
                Array.get(F32, w, 0), Array.get(U32, tgt, 0),
                Array.get(U32, edge, 1),
                Array.get(F32, hr, addr0), Array.get(F32, hv, addr0),
                cr, cv, r, v, tr, nnz, n_nodes, c,
                X{t, hslots, tmask, cfa, cfb, scale})

def seed_upd(sim: Sim) -> Sim:
  match sim:
    case Sim{edge, tgt, w, hr, hv, r, v, cr, cv, tr, +t, nnz, +n_nodes,
             +hslots, +tmask, cfa, cfb, scale, c}:
      upd_flat(U32.to_nat(n_nodes), 0, U32.sub(t, 1), U32.and(t, tmask),
               Array.get(F32, r, 0), Array.get(F32, v, 0),
               Array.get(F32, cr, 0), Array.get(F32, cv, 0),
               Array.get(F32, hr, 0), Array.get(F32, hv, 0),
               tr, edge, tgt, w, nnz, n_nodes, hslots, tmask, c,
               X{t, hslots, tmask, cfa, cfb, scale})

# the master loop: one iteration is one step t = 1..nstep.
# The trace index is t-1, and the history push slot is t & tmask.
def step_loop(+fuel: Nat, sim: Sim, +nnz1: Nat, +idx0: U32, +del0: U32,
              +hslots: U32, +tmask: U32) -> Sim:
  match fuel:
    case 0n:
      sim
    case 1n+f:
      step_loop(f,
                seed_upd(seed_coup(nnz1, sim, idx0, del0)),
                nnz1, idx0, del0, hslots, tmask)
