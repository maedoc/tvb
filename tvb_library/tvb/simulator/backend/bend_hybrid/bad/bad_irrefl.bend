# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The decider le_ok is hand-rolled; if it accepted a false claim, every law
# built on it would be vacuous.  x < x is false, so a proof of lt_ok(x, x)
# must be REJECTED.  Expected failure: Unit{} cannot inhabit Empty.
import Base
import ../router.bend as R

def bad_irrefl(x: Nat) -> R.lt_ok(x, x):
  match x:
    case 0n:
      Unit{}
    case 1n+p:
      bad_irrefl(p)
