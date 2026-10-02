# Functional test for the monitor model (router.bend Mon): a fast lane (k=1)
# and a slow lane (k=3) over 6 master ticks.  Per tick, the run records the
# SHARED monitor count and, for each lane, the sample index that lane
# CONTRIBUTES to tavg on that tick -- the post-step state the template
# accumulates (nb-hybrid-sim.py.mako L1031: tavg is accumulated AFTER the
# integrate, so the contribution of tick t is the lane's post-step newest).
# The slow lane's held samples repeat across the ticks it does not step,
# which is exactly the ZOH the temporal average averages over, while the
# count advances by exactly 1 per master tick for the whole run.
#
# Expected output pinned below (#|); run via tests/run_router.sh.
import Base
import ../router.bend as R

def show_lane(+l: R.Lane) -> String:
  "newest=" ++ Nat.show(R.lane_newest(l))

def show_lanes(ls: List<&2, R.Lane>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case h <> t:
      show_lanes(t, acc ++ " " ++ show_lane(h))

def run_ticks(t: Nat, +ls: List<&2, R.Lane>, +ks: List<&2, Nat>, +ps: List<&2, R.Proj>, +m: R.Mon, +acc: String) -> String:
  match t:
    case 0n:
      acc
    case 1n+p:
      +tk = R.tick(ls, ps)
      +mon = R.mon_tick(m)
      run_ticks(p, R.tick_lanes(tk), ks, ps, mon,
                acc ++ "\n" ++ "count=" ++ Nat.show(R.mon_n(mon))
                    ++ show_lanes(R.tick_lanes(tk), ""))

def main() -> IO(Unit):
  +lanes = R.init_lanes(1n <> 3n <> Nil{})
  +projs = {Nil{} : List<&2, R.Proj>}
  do IO<Unit>:
    IO.print(run_ticks(6n, lanes, 1n <> 3n <> Nil{}, projs, R.mon_init(), ""))
#|
#|count=1 newest=1 newest=0
#|count=2 newest=2 newest=0
#|count=3 newest=3 newest=1
#|count=4 newest=4 newest=1
#|count=5 newest=5 newest=1
#|count=6 newest=6 newest=2
