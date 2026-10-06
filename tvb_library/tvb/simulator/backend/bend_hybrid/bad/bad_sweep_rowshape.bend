# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The row-shape validator's negative: a RAGGED table -- row 0 carrying one
# parameter, row 1 carrying two -- validated at wp = 2.  rows_shape_ok
# folds is_eq(len(row), wp) over EVERY row; row 0 fails it, so the fold is
# False.  This is exactly the claim a missing shape conjunct would let
# through: a ragged table accepted, sim 0 silently running with field 1 at
# the 0.0 default instead of a real parameter.  Expected failure:
# rows_shape_ok computes to False, so {False == True} cannot close.
import Base
import ../sweep.bend as S

def bad_sweep_rowshape()
  -> {S.rows_shape_ok((0.5 <> Nil{}) <> (1.5 <> 2.5 <> Nil{}) <> Nil{}, 2n)
        == True{} : Bool}:
  {==}
