# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The per-lane rate validator's negative: a per-lane period list with a
# rate-0 ENTRY -- lane 0's monitor samples every ZERO master ticks.  Such
# a monitor counts nothing (rates_ok computes Nat.is_ge(0n, 1n) = False),
# and the per-own-step temporal average would divide by a stuck 0 forever.
# This is exactly the claim a missing rate bound would let through: the
# monitoring-variety layer's mtot_ok must reject it.  Expected failure:
# {mtot_ok(...) == True} cannot close (False vs True) -- the error must
# point at the {==} claim below, not at an import or a syntax error.
import Base
import ../mons.bend as MN
import ../router.bend as R

def bad_mon_period()
  -> {MN.mtot_ok(0n <> 2n <> Nil{},
                 MN.MonCfg{0n, 3n} <> Nil{},
                 R.Config{1n <> 2n <> Nil{}, Nil{}, 1n})
       == True{} : Bool}:
  {==}
