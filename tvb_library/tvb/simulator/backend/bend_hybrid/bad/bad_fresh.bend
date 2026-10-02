# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The mirror of Laws.clamp_necessary: it claims the UNGUARDED zero-delay
# read is fresh.  False, so the proof must be REJECTED.  Expected failure:
# {==} cannot close {False{} == True{} : Bool} in the base case.
import Base
import ../router.bend as R

def bad_fresh(n: Nat) -> {Nat.is_le(1n+n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      bad_fresh(p)
