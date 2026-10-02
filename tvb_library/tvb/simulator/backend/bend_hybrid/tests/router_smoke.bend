# Functional smoke test for router.bend: a fast lane (k=1), a slow lane
# (k=2), one projection 0 -> 1 with delay 1 and no averaging.  Six ticks.
# Expected lines are pinned below (#|); run via tests/run_router.sh.
import Base
import ../router.bend as R

def show_line(+l: R.Line) -> String:
  "i0=" ++ Nat.show(R.l_i0(l)) ++ " i1=" ++ Nat.show(R.l_i1(l)) ++ " num=" ++ Nat.show(R.l_num(l)) ++ "/" ++ Nat.show(R.l_den(l)) ++ " win=" ++ Nat.show(R.l_win(l))

def show_lines(ls: List<&2, R.Line>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case h <> t:
      show_lines(t, acc ++ " " ++ show_line(h))

def run_ticks(t: Nat, +ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>, +acc: String) -> String:
  match t:
    case 0n:
      acc
    case 1n+p:
      +tk = R.tick(ls, ps)
      run_ticks(p, R.tick_lanes(tk), ps,
                acc ++ "\n" ++ show_lines(R.tick_lines(tk), ""))

def main() -> IO(Unit):
  +lanes = R.init_lanes(1n <> 2n <> Nil{})
  +projs = {R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{} : List<&2, R.Proj>}
  do IO<Unit>:
    IO.print(run_ticks(6n, lanes, projs, ""))







#|
#| i0=0 i1=1 num=0/1 win=0
#| i0=1 i1=2 num=0/1 win=0
#| i0=2 i1=3 num=0/1 win=0
#| i0=3 i1=4 num=0/1 win=0
#| i0=4 i1=5 num=0/1 win=0
#| i0=5 i1=6 num=0/1 win=0
