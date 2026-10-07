# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The BOLD kind routing's negative: the claim that the TAVG constructor
# is received as BOLD.  mkind_is_bold(MKtavg{}) computes False{} (the
# constructor cover is disjoint -- a schedule is exactly ONE kind), so the
# kind mis-route claim cannot close.  This is exactly the claim the
# BOLD/tavg kind routing pins would let through if the routing were
# reversed.  Expected failure: {mkind_is_bold(...) == True} cannot close
# (False vs True) -- the error must point at the {==} claim below.
import Base
import ../mons.bend as MN

def bad_bold()
  -> {MN.mkind_is_bold(MN.MKtavg{}) == True{} : Bool}:
  {==}
