# Functional smoke test for coupling.bend STAGE A (COUPLING_LAWS_DESIGN.md
# families C1 + C2): the cvar-indexed tape plane and the cvar-selective
# routed read, on the getting-started heterogeneous network -- JansenRit's
# lane 0 with its 2 state variables (cvar tapes 'y0', 'y1' shown), FHN's
# lane 1 with its 1 ('xi'), the cross-model projection 'y1' -> 'xi'.
# Stage A pins the READ side: cvar_tape(tapes, L, v) is row (L, v) of the
# plane (C1), and edge_cells_cvar reads the routed window (ticks 1..2 of
# the (lo, hi] reading at d=1, w=2, newest 3) over the SOURCE cvar's tape
# -- svar 1 ('y1') at lane 0, NOT any other cvar (C2; a wrong-but-in-range
# source cvar changes the reading, last pin).  The couple_all fold and the
# untargeted-site law (C3/C4) are stage B/C -- NOT here.
# Expected lines are pinned below (#|); run via tests/run_coupling.sh.
import Base
import ../coupling.bend as C
import ../mconfig.bend as M
import ../router.bend as R
import ../hist.bend as H

def main() -> IO(Unit):
  +tapes : List<&2, List<&2, List<&2, F32>>> =
    {((0.5 <> 1.5 <> 2.5 <> Nil{}) <> (10.0 <> 11.0 <> 12.0 <> Nil{}) <> Nil{})
     <> ((20.0 <> 21.0 <> Nil{}) <> Nil{}) <> Nil{} : List<&2, List<&2, List<&2, F32>>>}
  +ls : List<&2, R.Lane> = {R.Lane{1n, 0n, 3n} <> Nil{} : List<&2, R.Lane>}
  +ly0 : List<&2, F32> = C.cvar_tape(tapes, 0n, 0n)
  +ly1 : List<&2, F32> = C.cvar_tape(tapes, 0n, 1n)
  +lxi : List<&2, F32> = C.cvar_tape(tapes, 1n, 0n)
  +pi : M.MProj = M.MProj{0n, 1n, 1n, 0n}
  +pi0 : M.MProj = M.MProj{0n, 1n, 0n, 0n}
  +win1 : List<&2, F32> = C.edge_cells_cvar(ls, pi, 1n, 2n, tapes, 0.0)
  +win0 : List<&2, F32> = C.edge_cells_cvar(ls, pi0, 1n, 2n, tapes, 0.0)
  +out : String = " " ++ Bool.show(Nat.is_eq(H.hist_len(ly0), 3n)) ++ "\n"
    ++ " " ++ Bool.show(Nat.is_eq(H.hist_len(ly1), 3n)) ++ "\n"
    ++ " " ++ Bool.show(Nat.is_eq(H.hist_len(lxi), 2n)) ++ "\n"
    ++ " " ++ Bool.show(F32.is_eq(H.hist_read(ly1, 2n, 0.0), 12.0)) ++ "\n"
    ++ " " ++ Bool.show(F32.is_eq(H.hist_read(lxi, 1n, 0.0), 21.0)) ++ "\n"
    ++ " " ++ Bool.show(F32.is_eq(H.hist_read(lxi, 2n, 0.0), 0.0)) ++ "\n"
    ++ " " ++ Bool.show(Nat.is_eq(H.hist_len(win1), 2n)) ++ "\n"
    ++ " " ++ Bool.show(F32.is_eq(H.hist_read(win1, 0n, 0.0), 11.0)) ++ "\n"
    ++ " " ++ Bool.show(F32.is_eq(H.hist_read(win1, 1n, 0.0), 12.0)) ++ "\n"
    ++ " " ++ Bool.show(F32.is_eq(H.hist_read(win0, 0n, 0.0), 11.0)) ++ "\n"
  do IO<Unit>:
    IO.print(out)

#| True
#| True
#| True
#| True
#| True
#| True
#| True
#| True
#| True
#| False
