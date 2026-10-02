# Co-simulation (macro-first) window, using ONLY the existing routing
# primitives -- no new constructors, no new laws needed:
#
#   * the slow subnet steps FIRST and pushes sample s (here s = 3);
#   * the fast subnet's micro-ticks r = 0..k-1 read it INTERPOLATED between
#     the two pushed window endpoints:  route_read(s, d=1, num=r, den=k)
#     -> i0 = s-1, i1 = s, alpha = r/k   (fresh by Laws.read_fresh, d >= 1
#     branch: i1 = s <= newest -- no clamp, no lag);
#   * the slow subnet's own input for its NEXT step is the anti-alias
#     average of the fast trajectory over the trailing window:
#     route_window(n, d=0, w=k) -> (n-k, n)   (the Q2 mode).
#
# In the CURRENT tvb-kh schedule (read-then-push), the mid-window
# interpolated read is impossible -- Laws.clamp_necessary is that fact as a
# theorem.  Macro-first makes it inhabitable; the price is that the slow's
# input must be windowed (duality of the two directions).
import Base
import ../router.bend as R

def show_line(+l: R.Line) -> String:
  "i0=" ++ Nat.show(R.l_i0(l)) ++ " i1=" ++ Nat.show(R.l_i1(l)) ++ " num=" ++ Nat.show(R.l_num(l)) ++ "/" ++ Nat.show(R.l_den(l))

def show_lines(ls: List<&2, R.Line>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case h <> t:
      show_lines(t, acc ++ " | " ++ show_line(h))

# fast micro-tick reads for r = 0 .. k-1, interpolated on the window
def mf_reads(r: Nat, +acc: List<&2, R.Line>) -> List<&2, R.Line>:
  match r:
    case 0n:
      acc
    case 1n++p:
      mf_reads(p, R.route_read(3n, 1n, p, 10n, 0n) <> acc)

def main() -> IO(Unit):
  +reads = {mf_reads(10n, Nil{}) : List<&2, R.Line>}
  +slow_input = R.route_window(20n, 0n, 10n)
  do IO<Unit>:
    IO.print("fast reads:  " ++ show_lines(reads, "") ++ "\n")
    IO.print("slow input:  lo=" ++ Nat.show(R.win_lo(slow_input)) ++ " hi=" ++ Nat.show(R.win_hi(slow_input)) ++ "\n")
#|fast reads:   | i0=2 i1=3 num=0/10 | i0=2 i1=3 num=1/10 | i0=2 i1=3 num=2/10 | i0=2 i1=3 num=3/10 | i0=2 i1=3 num=4/10 | i0=2 i1=3 num=5/10 | i0=2 i1=3 num=6/10 | i0=2 i1=3 num=7/10 | i0=2 i1=3 num=8/10 | i0=2 i1=3 num=9/10
#|
#|slow input:  lo=10 hi=20
#|
