# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The mirror of Laws.read_saturate: "the router wraps like a ring buffer,
# so a delay past the history lands on some slot modulo the size".  On a
# 0-deep history a wrapping read at delay 5 (ring size 2, say) would return
# slot 1; the router returns the IC slot 0 and two absurd delays coincide
# (the plateau).  If this proof were accepted, the plateau would be
# vacuous.  Expected failure: {==} cannot close the equation (distinct
# normal forms: Line{0n, 0n, 0n, 1n, 0n} vs Line{1n, 1n, 0n, 1n, 0n}).
import Base
import ../router.bend as R

def bad_wrap()
    -> {R.route_read(0n, 5n, 0n, 1n, 0n) == R.Line{1n, 1n, 0n, 1n, 0n} : R.Line}:
  {==}
