# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The connectome-sweep validator's negative: a row whose payload BREAKS
# the shared shape -- sim 0 carries ONE weight for the shared TWO-edge
# layout (indices [0, 1]).  cs_shape_ok folds pay_shape_ok over EVERY
# row; sim 0's weight count (1) fails its is_eq against the shared edge
# count (2), so the fold is False and the whole validator is False.
# This is exactly the claim a missing shared-shape conjunct would let
# through: a short payload accepted, sim 0 silently running with its
# missing edge's weight at the 0.0 default.  (The out-of-bounds-index
# arm is the router's own negative: csr_ok_bad_index rejects it inside
# the per-row csr_ok fold.)
# Expected failure: sweep_csr_ok computes to False, so {False == True}
# cannot close.
import Base
import ../sweep.bend as S
import ../router.bend as R

def bad_sweep_csr()
  -> {S.sweep_csr_ok(0n <> 1n <> 2n <> Nil{}, 0n <> 1n <> Nil{},
                     S.CsrPay{0.1 <> Nil{}, 0n <> 1n <> Nil{}}
                       <> S.CsrPay{0.3 <> 0.4 <> Nil{}, 2n <> 0n <> Nil{}}
                       <> Nil{},
                     R.Config{1n <> 2n <> Nil{},
                              R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{}, 4n})
        == True{} : Bool}:
  {==}
