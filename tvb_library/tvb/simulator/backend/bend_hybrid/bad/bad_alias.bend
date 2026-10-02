# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The mirror of Laws.read_distinct WITHOUT the horizon witness: it claims
# ANY two distinct delays read distinct i0 samples.  False, and the falsity
# is the IC fill: at n=0 the saturating subtraction collapses every delay
# to sample 0, so d=1 and d=2 both read i0=0 -- exactly the aliasing
# router.bend's csr comment warns about ("would alias two distinct delays
# onto the same buffer slot"), which le_ok(db, n) exists to exclude.
import Base
import ../router.bend as R

def bad_alias(n: Nat, da: Nat, db: Nat, +num: Nat, +den: Nat, +win: Nat,
              +h: {Nat.is_lt(da, db) == True{} : Bool})
    -> {Nat.is_ne(R.l_i0(R.route_read(n, da, num, den, win)),
                  R.l_i0(R.route_read(n, db, num, den, win))) == True{} : Bool}:
  Bool.fne({Nat.is_ne(R.l_i0(R.route_read(n, da, num, den, win)),
                      R.l_i0(R.route_read(n, db, num, den, win))) == True{} : Bool},
           Bool.fne({Nat.is_lt(da, db) == True{} : Bool}, h))
