# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The mirror of Laws.blend_order with the multiplication's operands
# SWAPPED: value-equal in exact arithmetic, DIFFERENT in IEEE-754
# rounding, and different as a term. If this proof were accepted, the
# op-order contract would be vacuous. Expected failure: {==} cannot close
# the equation (distinct normal forms).
import Base
import ../kernel.bend as K

def bad_blend_regroup(x0: F32, x1: F32, a: F32)
    -> {K.blend(x0, x1, a) == F32.add(F32.mul(F32.sub(x1, x0), a), x0) : F32}:
  {==}
