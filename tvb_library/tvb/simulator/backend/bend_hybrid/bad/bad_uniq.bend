# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# A concrete falsity witness for ok_no_clash WITHOUT writes_unique: two
# IDENTICAL projections (same src, tgt, delay, slot) at indices 0 and 1
# of a two-element list.  Their coupling slots are equal (both tc=0), so
# the disequality is_ne(0, 0) reduces to False == True -- unprovable.
# This is exactly the double-write ok's writes_unique conjunct excludes:
# a float += into slot 0 happening twice per tick, order-dependent.
import Base
import ../router.bend as R

def bad_uniq()
    -> {Nat.is_ne(R.proj_tc(R.nth_proj(
                     {R.Proj{0n, 0n, 1n, 0n, 0n} <> R.Proj{0n, 0n, 1n, 0n, 0n} <> Nil{}
                      : List<&2, R.Proj>}, 0n)),
                  R.proj_tc(R.nth_proj(
                     {R.Proj{0n, 0n, 1n, 0n, 0n} <> R.Proj{0n, 0n, 1n, 0n, 0n} <> Nil{}
                      : List<&2, R.Proj>}, 1n))) == True{} : Bool}:
  {==}
