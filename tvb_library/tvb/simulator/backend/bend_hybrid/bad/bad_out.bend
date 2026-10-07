# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The out_route claim at an OUT-OF-RANGE (i, s) cell: subnet 2 of sim 0 in
# a 2-subnet output table.  The (0, 2) cell is past the block's series --
# the un-routing read answers the empty series (the default-read
# convention) -- but the claim asserts it equals a REAL series (the
# non-empty [4, 5]).  This is exactly the claim a missing inner bounds
# witness would let through: a fabricated slice index reading another
# subnet's (or no) series.  Expected failure: {==} cannot close (Nil vs a
# non-empty cons).
import Base
import ../sweep.bend as S

def OUT_B0() -> List<&2, List<&2, F32>>:
  (0.0 <> 1.0 <> Nil{}) <> (2.0 <> 3.0 <> Nil{}) <> Nil{}

def bad_out()
  -> {S.out_slice(OUT_B0() <> Nil{}, 0n, 2n) == 4.0 <> 5.0 <> Nil{}
      : List<&2, F32>}:
  {==}
