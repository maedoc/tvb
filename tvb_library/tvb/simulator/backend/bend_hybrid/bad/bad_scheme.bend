# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The scheme validator's negative: the getting-started network with the
# per-lane scheme assignment [0, 2] against a TWO-entry scheme table.
# Lane 1's id 2 indexes PAST the table: schemes_ok folds is_lt(2, 2) =
# False, so the whole conjunction is False.  This is exactly the claim a
# missing scheme-dimension bound would let through: lane 1's integrator
# read indexing past the scheme table.  (Expected failure:
# {scheme_ok(...) == True} cannot close -- False vs True.)
import Base
import ../mconfig.bend as M
import ../router.bend as R

def bad_scheme()
  -> {M.scheme_ok(0n <> 1n <> Nil{},
                  0n <> 2n <> Nil{},
                  2n <> 1n <> Nil{},
                  M.mview(R.Proj{0n, 1n, 0n, 0n, 0n} <> Nil{},
                          0n <> Nil{},
                          0n <> Nil{}),
                  R.Config{1n <> 1n <> Nil{},
                           R.Proj{0n, 1n, 0n, 0n, 0n} <> Nil{},
                           1n})
       == True{} : Bool}:
  {==}
