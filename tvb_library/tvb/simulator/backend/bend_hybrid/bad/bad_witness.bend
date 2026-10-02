# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# checked_read demands a witness that the delay fits the published history.
# d = 5 > n = 3 is out of history, so the witness cannot be fabricated and
# this call must be REJECTED.  Expected failure: le_ok(5,3) is Empty, and
# le_refl(3) : le_ok(3,3) = Unit does not inhabit it.
import Base
import ../router.bend as R

def bad_witness() -> R.Line:
  R.checked_read(3n, 5n, 0n, 1n, 0n, R.le_refl(3n))
