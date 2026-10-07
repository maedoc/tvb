# Functional smoke test for mons.bend: the monitoring-variety layer.
# Pins the rate-count story concretely: a rate-3 monitor over 10 master
# ticks counts 3 (samples at ticks 3, 6, 9 -- tick 0 contributes
# nothing), a rate-0 count over 0 ticks is 0 (the boundary convention),
# a lane-period monitor (rate 2) over 5 ticks counts the lane's 2 NEW
# publications beside the lane's IC count 1 (the lane is at 3), the
# validator accepts the well-formed monitor set and rejects the
# out-of-range lane and the rate-0 monitor, and the divisor pair: at
# rate 3 over 6 ticks the monitor divides by its OWN count 2 while the
# shared master count is 6.  Expected lines are pinned below (#|); run
# via tests/run_mons.sh.
import Base
import ../mons.bend as MN
import ../router.bend as R

def main() -> IO(Unit):
  +c : R.Config = R.Config{1n <> 2n <> Nil{}, Nil{}, 1n}
  +good : List<&2, MN.MonCfg>
    = MN.MonCfg{0n, 3n} <> MN.MonCfg{1n, 2n} <> Nil{}
  +badlane : List<&2, MN.MonCfg> = MN.MonCfg{2n, 3n} <> Nil{}
  +badrate : List<&2, MN.MonCfg> = MN.MonCfg{0n, 0n} <> Nil{}
  +out : String = " " ++ Nat.show(MN.mon_count(10n, 3n)) ++ "\n"
    ++ " " ++ Nat.show(MN.mon_count(0n, 5n)) ++ "\n"
    ++ " " ++ Nat.show(MN.mon_count(5n, 2n)) ++ "\n"
    ++ " " ++ Nat.show(R.lane_newest(R.steps(5n, R.Lane{2n, 1n, 1n}))) ++ "\n"
    ++ " " ++ Bool.show(MN.mons_ok(c, good)) ++ "\n"
    ++ " " ++ Bool.show(MN.mons_ok(c, badlane)) ++ "\n"
    ++ " " ++ Bool.show(MN.mons_ok(c, badrate)) ++ "\n"
    ++ " " ++ Nat.show(MN.mon_count(6n, 3n)) ++ "\n"
    ++ " " ++ Nat.show(R.mon_n(R.mon_ticks(6n, 1n <> Nil{}, R.mon_init()))) ++ "\n"
  do IO<Unit>:
    IO.print(out)

#| 3
#| 0
#| 2
#| 3
#| True
#| False
#| False
#| 2
#| 6
