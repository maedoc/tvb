# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The cvar validator's negative: the getting-started network (cortex
# cvar count 2, thalamus cvar count 1) with the projection's TARGET
# cvar resolved to index 1 of the 1-cvar thalamus model -- the named
# cvar 'xi' mistyped as a variable that does not exist in the target
# model.  mc_ok's target-cvar fold computes is_lt(1, 1) = False, so the
# whole conjunction is False.  This is exactly the claim a missing
# model-relative bound would let through: the coupling write indexing
# past the target model's cvar plane.  Expected failure:
# {mc_ok(...) == True} cannot close (False vs True).
import Base
import ../mconfig.bend as M
import ../router.bend as R

def bad_cvar()
  -> {M.mc_ok(2n <> 1n <> Nil{},
              M.mview(R.Proj{0n, 1n, 0n, 0n, 0n} <> Nil{},
                      0n <> Nil{},
                      1n <> Nil{}),
              R.Config{1n <> 1n <> Nil{},
                       R.Proj{0n, 1n, 0n, 0n, 0n} <> Nil{},
                       1n})
       == True{} : Bool}:
  {==}
