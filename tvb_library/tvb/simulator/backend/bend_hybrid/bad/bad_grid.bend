# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The grid's silent-failure modes, rejected by the grid layer:
#   (1) bad_len: an EMPTY dimension sweeps NOTHING -- the product of the
#       lengths is 0 grid points, not 2.  A claim that crams points out
#       of an empty range is the "grid with a hole" bug.
#   (2) bad_ok: the validator REJECTS the empty dimension -- grid_ok's
#       nonempty fold is load-bearing (an empty range makes the mixed-
#       radix split divide by 0).
#   (3) bad_wrap: an OUT-OF-RANGE index is REJECTED, not wrapped -- grid
#       point 4 of a 4-point grid (i == total) is not the first grid
#       point.  The past-the-end walk reads the default 0.0 (the
#       default-read convention), so the row is [0.0, 3.5], never a
#       real point's row; the guarded read grid_point makes the claim
#       unconditionally UNSTATABLE anyway (the lt_ok witness cannot be
#       fabricated for i >= total).
# Expected failure: {==} cannot close any of the three.
import Base
import ../sweep.bend as S
import ../router.bend as R

def BADGRID() -> List<&2, List<&2, F32>>:
  (0.5 <> 1.5 <> Nil{}) <> (2.5 <> 3.5 <> Nil{}) <> Nil{}

def BADCFG() -> R.Config:
  R.Config{1n <> 2n <> Nil{}, R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{}, 4n}

def bad_len()
  -> {S.grid_len(Nil{} <> BADGRID()) == 2n : Nat}:
  {==}

def bad_ok()
  -> {S.grid_ok(Nil{} <> BADGRID(), BADCFG()) == True{} : Bool}:
  {==}

def bad_wrap()
  -> {S.grid_row(BADGRID(), 4n) == 0.5 <> 2.5 <> Nil{}
      : List<&2, F32>}:
  {==}
