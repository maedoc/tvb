# Laws for the Bend MontbrioPazoRoxin hybrid prototype.
#
# This file is the written specification; PROOF.bend proves it, and
# `bend PROOF.bend --verdict` re-checks the proofs with the BendTT kernel.
#
# -------------------------------------------------------------------------
# What Bend 2.0 can and cannot prove
#
# `{==}` is STRUCTURAL reflexivity: it succeeds when both sides reduce to the
# same term.  Measured on bend 2.0.34:
#
#   {U32.sub(16, 1) == 15 : U32}            provable   (integer arithmetic
#                                                 normalises)
#   {F32.add(0.0, 0.0) == 0.0 : F32}         NOT provable
#   {F32.mul(0.0, 7.0) == 0.0 : F32}         NOT provable
#   {F32.div(0.0, 1.0) == 0.0 : F32}         NOT provable
#   {clamp_lo(0.0, 0.0) == 0.0 : F32}        NOT provable (a match on a
#                                                 concrete Bool does not reduce)
#
# So no float VALUE claim -- not even "0.0 + 0.0 == 0.0" -- is provable here.
# The laws below are therefore of two kinds:
#
#   1. structural identities that pin the arithmetic to the model's expression
#      string, term for term and in the same association.  These ARE the
#      fidelity contract, and a mistranscribed equation fails them.  (IEEE
#      multiplication is commutative and exact, so `2*V*r` and `2*r*V` agree in
#      value; the law still pins the order so that a future edit cannot silently
#      regroup the sum, which would change rounding.)
#   2. integer laws about the delayed read, which normalise and are proved.
#
# The numeric claims that Bend cannot check -- the fixed-point property, the
# clamp actually firing, the coupling product being 2*3=6 -- are checked
# numerically instead, by compare_montbrio.py against a float32 numba kernel
# that mirrors the same expression.  That is the division of labour between the
# two checkers, not a gap in either.
# -------------------------------------------------------------------------
import ./mcore.bend as Core
import ./mengine.bend as Eng

# --------------------------------------------------------------------------
# 1. the drift IS the model's expression
# --------------------------------------------------------------------------

# "r": "1/tau * ( Delta / (pi * tau) + 2 * V * r)"
law drift_is_model_expression_r:
  {Core.dr_of(0.25, F32.neg(1.5), 2.0, 1.0)
      == F32.mul(F32.div(1.0, 2.0),
                 F32.add(F32.div(1.0, F32.mul(F32.pi(), 2.0)),
                         F32.mul(F32.mul(2.0, F32.neg(1.5)), 0.25))) : F32}

# "V": "1/tau * ( V*V - pi*pi*tau*tau*r*r + eta + J*tau*r + I
#                + cr*Coupling_Term_r + cv*Coupling_Term_V )"
# with every one of the eight terms distinct, so a dropped or swapped term
# cannot go unnoticed
law drift_is_model_expression_v:
  {Core.dv_of(0.25, F32.neg(1.5), 2.0, F32.neg(5.0), 15.0, 0.5, 1.0, 0.5, 3.0, F32.neg(2.0))
      ==       F32.mul(F32.div(1.0, 2.0), F32.add(F32.add(F32.add(F32.add(F32.add(F32.sub(F32.mul(F32.neg(1.5), F32.neg(1.5)), F32.mul(F32.mul(F32.mul(F32.mul(F32.mul(F32.pi(), F32.pi()), 2.0), 2.0), 0.25), 0.25)), F32.neg(5.0)), F32.mul(F32.mul(15.0, 2.0), 0.25)), 0.5), F32.mul(1.0, 3.0)), F32.mul(0.5, F32.neg(2.0)))) : F32}

# with no incoming coupling the drift is the model expression with the two
# coupling terms contributing literal zeros.  Bend cannot evaluate `0.0 * 0.0`
# to `0.0`, so this law pins the STRUCTURE (the terms are there, in position,
# and vanish) while compare_montbrio.py checks the value numerically.
law zero_coupling_is_uncoupled:
  {Core.dv_of(0.25, F32.neg(1.5), 2.0, F32.neg(5.0), 15.0, 0.5,
                 0.0, 0.0, 0.0, 0.0)
      == F32.mul(F32.div(1.0, 2.0),
                 F32.add(F32.add(F32.add(F32.add(F32.add(
                            F32.sub(F32.mul(F32.neg(1.5), F32.neg(1.5)),
                                    F32.mul(F32.mul(F32.mul(F32.mul(F32.mul(
                                          F32.pi(), F32.pi()), 2.0), 2.0),
                                                  0.25), 0.25)),
                            F32.neg(5.0)),
                            F32.mul(F32.mul(15.0, 2.0), 0.25)), 0.5),
                        F32.mul(0.0, 0.0)), F32.mul(0.0, 0.0))) : F32}

# the fixed point, in the only form Bend can state: at the rest state
# (r, V) = (0, 0) every state-dependent factor of the drift is a literal zero
law drift_fixed_point_r:
  {Core.dr_of(0.0, 0.0, 1.0, 0.0)
      == F32.mul(F32.div(1.0, 1.0),
                 F32.add(F32.div(0.0, F32.mul(F32.pi(), 1.0)),
                         F32.mul(F32.mul(2.0, 0.0), 0.0))) : F32}

law drift_fixed_point_v:
  {Core.dv_of(0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0)
      ==       F32.mul(F32.div(1.0, 1.0), F32.add(F32.add(F32.add(F32.add(F32.add(F32.sub(F32.mul(0.0, 0.0), F32.mul(F32.mul(F32.mul(F32.mul(F32.mul(F32.pi(), F32.pi()), 1.0), 1.0), 0.0), 0.0)), 0.0), F32.mul(F32.mul(0.0, 1.0), 0.0)), 0.0), F32.mul(1.0, 0.0)), F32.mul(0.0, 0.0))) : F32}

# --------------------------------------------------------------------------
# 2. the delayed read: slot = (t - 1 - idelay) mod H, with H a power of two
#
# `e_slot` takes a packed edge word (idx in the low 16 bits, idelay in the high
# 16) and the 1-based tick.  Here H = 16, so tmask = 15.
# --------------------------------------------------------------------------

# the packing round-trips: idx 7 and delay 3 pack to 0x00030007
law packed_edge_roundtrip:
  {U32.or(Eng.e_idx(196615), U32.shln(Eng.e_delay(196615), 16n)) == 196615
      : U32}

law packed_edge_idx:
  {Eng.e_idx(196615) == 7 : U32}

law packed_edge_delay:
  {Eng.e_delay(196615) == 3 : U32}

# a zero-delay edge at tick 1 reads slot 0: the state already pushed at tick 0
law ring_zero_delay_first_tick:
  {Eng.e_slot(7, 1, 15) == 0 : U32}

# at tick 1 a delay of 3 would read step -2, which wraps to the oldest slot --
# the one the reference fills with the initial state: (1 - 1 - 3) mod 16 == 13
law ring_wraps_before_the_start:
  {Eng.e_slot(196615, 1, 15) == 13 : U32}

# a delay of 4 addresses one slot earlier than a delay of 3, so at a fixed tick
# two delays cannot alias onto the same step
law ring_delays_are_offset:
  {U32.sub(Eng.e_slot(196615, 1, 15), Eng.e_slot(262151, 1, 15)) == 1 : U32}

# the slot advances by exactly one per tick at fixed delay
law ring_advances_one_slot_per_tick:
  {U32.sub(Eng.e_slot(7, 2, 15), Eng.e_slot(7, 1, 15)) == 1 : U32}

# and wraps from the oldest slot back to 0
law ring_wraps_around:
  {Eng.e_slot(7, 17, 15) == 0 : U32}
