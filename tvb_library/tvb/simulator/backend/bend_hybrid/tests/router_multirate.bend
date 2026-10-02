# Multi-rate smoke test: lanes k=1 (fast) and k=2 (slow).  Projections:
#   p1: slow -> fast, delay 0  (the clamp: i1=i0, num zeroed)
#   p2: slow -> fast, delay 1  (2-point read, fraction = position in period)
#   p3: slow -> fast, delay 1, win=2  (Q2 anti-alias window, carried as Nat)
# Expected lines are pinned below (#|).
import Base
import ../router.bend as R

def show_line(+l: R.Line) -> String:
  "i0=" ++ Nat.show(R.l_i0(l)) ++ " i1=" ++ Nat.show(R.l_i1(l)) ++ " num=" ++ Nat.show(R.l_num(l)) ++ "/" ++ Nat.show(R.l_den(l)) ++ " win=" ++ Nat.show(R.l_win(l))

def show_lines(ls: List<&2, R.Line>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case h <> t:
      show_lines(t, acc ++ " | " ++ show_line(h))

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
  +projs = {R.Proj{1n, 0n, 0n, 0n, 0n} <> R.Proj{1n, 0n, 1n, 0n, 1n} <> R.Proj{1n, 0n, 1n, 2n, 2n} <> Nil{} : List<&2, R.Proj>}
  do IO<Unit>:
    IO.print(run_ticks(6n, lanes, projs, ""))
#|
#| | i0=0 i1=0 num=0/2 win=0 | i0=0 i1=0 num=1/2 win=0 | i0=0 i1=0 num=1/2 win=2
#| | i0=1 i1=1 num=0/2 win=0 | i0=0 i1=1 num=0/2 win=0 | i0=0 i1=1 num=0/2 win=2
#| | i0=1 i1=1 num=0/2 win=0 | i0=0 i1=1 num=1/2 win=0 | i0=0 i1=1 num=1/2 win=2
#| | i0=2 i1=2 num=0/2 win=0 | i0=1 i1=2 num=0/2 win=0 | i0=1 i1=2 num=0/2 win=2
#| | i0=2 i1=2 num=0/2 win=0 | i0=1 i1=2 num=1/2 win=0 | i0=1 i1=2 num=1/2 win=2
#| | i0=3 i1=3 num=0/2 win=0 | i0=2 i1=3 num=0/2 win=0 | i0=2 i1=3 num=0/2 win=2
