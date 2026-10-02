# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The mirror of Laws.count_shared: a "fixed" per-subnet tavg counter that
# increments once per LANE per master tick (n lanes -> count advances by n
# per tick) instead of once per tick for the whole run.  For a two-lane
# network the count after t ticks would be 2t, so the claim "the count
# advances by 1 per master tick" is FALSE here -- the per-lane counter
# divides every subnet's temporal average by a growing factor (2x for two
# lanes), silently rescaling all monitor output.  Expected failure: the
# base case closes but the step case cannot close
# {2n * (1n+p) == 1n + 2n * p}-style goals without a missing lemma -- and
# more fundamentally the goal is false.
import Base
import ../router.bend as R

def lane_count(+ls: List<&2, Nat>, +m: R.Mon) -> R.Mon:
  match ls:
    case Nil{}:
      m
    case _ <> t:
      R.Mon{1n+R.mon_n(lane_count(t, m))}

def lane_ticks(t: Nat, +ls: List<&2, Nat>, +m: R.Mon) -> R.Mon:
  match t:
    case 0n:
      m
    case 1n+p:
      lane_ticks(p, ls, lane_count(ls, m))

def bad_count(t: Nat, +ls: List<&2, Nat>, +m: R.Mon)
    -> {R.mon_n(lane_ticks(t, ls, m)) == Nat.add(t, R.mon_n(m)) : Nat}:
  match t:
    case 0n:
      {==}
    case 1n+p:
      bad_count(p, ls, lane_count(ls, m))
