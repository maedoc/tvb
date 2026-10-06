# Functional smoke test for sweep.bend: a literal 3-sim parameter table, a
# literal 8-run table, and the fixed 8-wide fan over it.  Pins the fan's
# coverage (n = 3 gathers exactly runs 0..2, n = 8 gathers all 8, n = 0
# gathers nothing), the gate (lane 2 of a 3-sweep runs, lane 5 does not),
# and the row routing (sim 2's parameter IS word 2, through the
# witness-carrying swept_param; the reference read agrees on word 1).
# Expected lines are pinned below (#|); run via tests/run_sweep.sh.
import Base
import ../sweep.bend as S
import ../router.bend as R

def main() -> IO(Unit):
  +runs = {"r0" <> "r1" <> "r2" <> "r3" <> "r4" <> "r5" <> "r6" <> "r7" <> Nil{} : List<&2, String>}
  +tbl = {0.5 <> 1.5 <> 2.5 <> Nil{} : List<&2, F32>}
  +r2 : String = S.fan_lane(3n, 2n, k => S.str_nth(runs, k))
  +r5 : String = S.fan_lane(3n, 5n, k => S.str_nth(runs, k))
  +p2 : Bool = F32.is_eq(S.swept_param(tbl, 2n, R.le_refl(3n)), 2.5)
  +p1 : Bool = F32.is_eq(S.sweep_word(tbl, 1n), 1.5)
  +out : String = " " ++ S.gather(S.fan8(3n, runs)) ++ "\n"
    ++ " " ++ S.gather(S.fan8(8n, runs)) ++ "\n"
    ++ " " ++ S.gather(S.fan8(0n, runs)) ++ "\n"
    ++ " " ++ r2 ++ "\n"
    ++ " " ++ r5 ++ "\n"
    ++ " " ++ Bool.show(p2) ++ "\n"
    ++ " " ++ Bool.show(p1) ++ "\n"
  do IO<Unit>:
    IO.print(out)

#| r0r1r2
#| r0r1r2r3r4r5r6r7
#| 
#| r2
#| 
#| True
#| True
