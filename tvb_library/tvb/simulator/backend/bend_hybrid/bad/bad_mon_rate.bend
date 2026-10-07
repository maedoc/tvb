# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The rate validator's negative: a monitor with rate 0 -- sample every
# ZERO master ticks.  Such a monitor samples never (mon_rate_ok computes
# Nat.is_ge(0n, 1n) = False), so its sample count stays stuck at 0 and
# the per-own-step temporal average would divide by 0 forever.  This is
# exactly the claim a missing rate bound would let through: the
# monitor-variety layer's mons_ok must reject it.  Expected failure:
# {mons_ok(...) == True} cannot close (False vs True).
import Base
import ../mons.bend as MN
import ../router.bend as R

def bad_mon_rate()
  -> {MN.mons_ok(R.Config{1n <> 1n <> Nil{}, Nil{}, 1n},
                 MN.MonCfg{0n, 0n} <> Nil{})
       == True{} : Bool}:
  {==}
