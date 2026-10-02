# MontbrioPazoRoxin hybrid simulation core, pure (no IO).
#
# Port of the numba hybrid kernel for one subnet, one mode, Heun integrator,
# CSR sparse connectome with per-edge integer-step delays.
#
# Reference semantics (tvb_library/tvb/simulator/backend/templates/
# nb-hybrid-sim.py.mako, single-dt path):
#
#   coupling, per target node j, over its in-edges:
#       wsum  = sum_over_edges( w[e] * src[var][s, (t-1-idelay[e]) mod H] )
#       wsum  = a * wsum + b            (Linear cfun post)
#       wsum *= scale                  (projection scale; target scale ts = 1)
#       c[var][j] += wsum
#   drift (models/infinite_theta.py MontbrioPazoRoxin):
#       dr = 1/tau * ( Delta/(pi*tau) + 2*V*r )
#       dV = 1/tau * ( V*V - pi*pi*tau*tau*r*r + eta + J*tau*r + I
#                      + cr*Coupling_Term_r + cv*Coupling_Term_V )
#   Heun: i1 = clamp(x + dt*d0); d1 = drift(i1, SAME c); x = clamp(x + dt/2*(d0+d1))
#   clamp: state_variable_boundaries = {r: [0, inf]} -> `if r < 0: r = 0`
#   push: the state after step t goes to history slot t mod H
#
# Bend idioms this file relies on (all verified against bend 2.0.34):
#   * no field access syntax: every read of a datatype field is its own
#     accessor def that matches on the parameter
#   * loops are recursion; the SHRINKING argument must come first and
#     everything after it is free, so the threaded Array may change per step
#   * `Array.get` returns a dependent pair `Array<T> & T`, and a `match` may
#     only inspect a parameter -- so the pair is threaded as an ARGUMENT and
#     matched on the next call.  Bend forbids mutual recursion, so such a loop
#     must be written as a SINGLE def
#   * an Array is a `Type` (single owner): never marked `+`, always threaded
#   * operators demand an explicit type annotation, so arithmetic uses the F32
#     verbs -- exactly the `-ffp-contract=off` discipline the C++ core needs:
#     one call per operator, no fused reassociation
#   * negative literals are written F32.neg(x); there is no `if`, so a
#     condition is Bool.pick or a match on True{}/False{}
import Base

# --------------------------------------------------------------------------
# Cfg: the per-node model parameters and the coupling values for one step.
# One subnet, one mode: no mode dimension anywhere.
# --------------------------------------------------------------------------

type Cfg is Data:
  C{dt: F32, tau: F32, delta: F32, eta: F32, jj: F32, ii: F32,
   ccr: F32, ccv: F32}

type RV is Data:
  RV{r: F32, v: F32}

def c_dt(c: Cfg) -> F32:
  match c:
    case C{dt, tau, delta, eta, jj, ii, ccr, ccv}: dt

def c_tau(c: Cfg) -> F32:
  match c:
    case C{dt, tau, delta, eta, jj, ii, ccr, ccv}: tau

def c_delta(c: Cfg) -> F32:
  match c:
    case C{dt, tau, delta, eta, jj, ii, ccr, ccv}: delta

def c_eta(c: Cfg) -> F32:
  match c:
    case C{dt, tau, delta, eta, jj, ii, ccr, ccv}: eta

def c_j(c: Cfg) -> F32:
  match c:
    case C{dt, tau, delta, eta, jj, ii, ccr, ccv}: jj

def c_i(c: Cfg) -> F32:
  match c:
    case C{dt, tau, delta, eta, jj, ii, ccr, ccv}: ii

def c_ccr(c: Cfg) -> F32:
  match c:
    case C{dt, tau, delta, eta, jj, ii, ccr, ccv}: ccr

def c_ccv(c: Cfg) -> F32:
  match c:
    case C{dt, tau, delta, eta, jj, ii, ccr, ccv}: ccv

def rv_r(x: RV) -> F32:
  match x:
    case RV{r, v}: r

def rv_v(x: RV) -> F32:
  match x:
    case RV{r, v}: v

# --------------------------------------------------------------------------
# decoding: a u32 from the job file is a fixed-point signed value
# (value = sign * u / scale).  Bend has no float bit-reinterpretation --
# `F32.to_u32` is a numeric truncation, not a bit cast -- so the job file
# carries floats as scaled integers.
# --------------------------------------------------------------------------

def dec_neg(+u: U32) -> Bool:
  U32.is_ge(u, 2147483648)

def dec_mag(+u: U32, +neg: Bool) -> U32:
  Bool.pick(U32, neg, U32.sub(0, u), u)

def apply_sign(+x: F32, +neg: Bool) -> F32:
  match neg:
    case True{}:
      F32.neg(x)
    case False{}:
      x

def dec_f32(+u: U32, +scale: F32) -> F32:
  # the encoding is two's complement: u >= 2^31 means negative, and the
  # magnitude is 0 - u (mod 2^32)
  +neg : Bool = dec_neg(u)
  mag = dec_mag(u, neg)
  apply_sign(F32.div(F32.from_nat(U32.to_nat(mag)), scale), neg)

# --------------------------------------------------------------------------
# Montbrio drift (models/infinite_theta.py, MontbrioPazoRoxin)
# --------------------------------------------------------------------------

def pi_tau(+tau: F32) -> F32:
  F32.mul(F32.pi(), tau)

# The drift below is a LITERAL transcription of the model's expression strings:
#
#   "r": "1/tau * ( Delta / (pi * tau) + 2 * V * r)"
#   "V": "1/tau * ( V*V - pi*pi*tau*tau*r*r + eta + J * tau * r + I
#                  + cr * Coupling_Term_r + cv * Coupling_Term_V)"
#
# evaluated left to right with one rounding per operator, exactly as the numba
# kernel does when it embeds the same string.  That matters twice over: an
# algebraically equivalent regrouping is NOT bit-identical, and Bend has no F64
# or fused-multiply-add to hide the difference, so the only safe port is to
# mirror the parenthesisation rather than to improve on it.
def dr_of(+r: F32, +v: F32, +tau: F32, +delta: F32) -> F32:
  F32.mul(F32.div(1.0, tau),
          F32.add(F32.div(delta, F32.mul(F32.pi(), tau)),
                  F32.mul(F32.mul(2.0, v), r)))

# The model expression, term for term (models/infinite_theta.py,
# MontbrioPazoRoxin.state_variable_dfuns):
#   1/tau * ( V*V - pi*pi*tau*tau*r*r + eta + J*tau*r + I
#             + cr*Coupling_Term_r + cv*Coupling_Term_V )
# `cr`/`cv` are the model PARAMETERS and `c_r`/`c_v` the incoming coupling
# values, so both factors are needed.
def dv_of(+r: F32, +v: F32, +tau: F32, +eta: F32, +jj: F32, +ii: F32,
          +cr: F32, +cv: F32, +c_r: F32, +c_v: F32) -> F32:
  # strict left-to-right summation of the eight terms, one rounding per
  # operator -- the same order the numba kernel gets from the model string
  +quad : F32 = F32.mul(F32.mul(F32.mul(F32.mul(F32.mul(F32.pi(), F32.pi()),
                                                    tau), tau), r), r)
  +a1 : F32 = F32.sub(F32.mul(v, v), quad)
  +a2 : F32 = F32.add(a1, eta)
  +a3 : F32 = F32.add(a2, F32.mul(F32.mul(jj, tau), r))
  +a4 : F32 = F32.add(a3, ii)
  +a5 : F32 = F32.add(a4, F32.mul(cr, c_r))
  +a6 : F32 = F32.add(a5, F32.mul(cv, c_v))
  F32.mul(F32.div(1.0, tau), a6)

def clamp_lo(+x: F32, +lo: F32) -> F32:
  Bool.pick(F32, F32.is_lt(x, lo), lo, x)

# --------------------------------------------------------------------------
# one Heun step on one node.  The coupling is a PARAMETER, not recomputed, so
# both stages see the same value -- the property nb_hybrid relies on.
# --------------------------------------------------------------------------

def heun_cell(+r0: F32, +v0: F32, +c: Cfg, +c_r: F32, +c_v: F32) -> RV:
  +tau : F32 = c_tau(c)
  +dt : F32 = c_dt(c)
  +cr : F32 = c_ccr(c)
  +cv : F32 = c_ccv(c)
  +eta : F32 = c_eta(c)
  +jj : F32 = c_j(c)
  +ii : F32 = c_i(c)
  +delta : F32 = c_delta(c)
  # stage 0
  +d0r : F32 = dr_of(r0, v0, tau, delta)
  +d0v : F32 = dv_of(r0, v0, tau, eta, jj, ii, cr, cv, c_r, c_v)
  # stage 1 predictor, clamped on r (boundary lo = 0.0)
  +i1r : F32 = clamp_lo(F32.add(r0, F32.mul(dt, d0r)), 0.0)
  +i1v : F32 = F32.add(v0, F32.mul(dt, d0v))
  +d1r : F32 = dr_of(i1r, i1v, tau, delta)
  +d1v : F32 = dv_of(i1r, i1v, tau, eta, jj, ii, cr, cv, c_r, c_v)
  +half : F32 = F32.mul(dt, 0.5)
  RV{clamp_lo(F32.add(r0, F32.mul(half, F32.add(d0r, d1r))), 0.0),
     F32.add(v0, F32.mul(half, F32.add(d0v, d1v)))}
