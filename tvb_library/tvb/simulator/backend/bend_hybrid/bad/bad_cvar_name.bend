# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The name-resolution validator's negative: the getting-started network
# (JansenRit ["y0".."y5"], FHN ["xi","eta","alpha","beta"]) with the named
# projection's TARGET cvar "nu" -- a variable the FHN target model does
# not have.  find_name resolves the unknown name to the junk index (the
# name list's length, 4), and mc_ok's target-cvar bound computes
# is_lt(4, 4) = False, so the whole conjunction is False.  This is
# exactly the claim a missing name-resolution check would let through:
# the coupling write indexing past the target model's state-variable
# plane under a name that LOOKS plausible.  (Expected failure:
# {mc_ok(...) == True} cannot close -- False vs True.)
import Base
import ../mconfig.bend as M
import ../router.bend as R

def bad_cvar_name()
  -> {M.mc_ok(6n <> 4n <> Nil{},
              M.mnview(M.NProj{0n, 1n, "y1", "nu"} <> Nil{},
                       ("y0" <> "y1" <> "y2" <> "y3" <> "y4" <> "y5" <> Nil{})
                         <> ("xi" <> "eta" <> "alpha" <> "beta" <> Nil{})
                         <> Nil{}),
              R.Config{1n <> 1n <> Nil{},
                       R.Proj{0n, 1n, 0n, 0n, 0n} <> Nil{},
                       1n})
       == True{} : Bool}:
  {==}
