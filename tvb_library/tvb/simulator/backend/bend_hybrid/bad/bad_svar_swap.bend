# NEGATIVE CONTROL -- this file MUST NOT typecheck, and it MUST fail AT
# ITS CLAIM (a {==} mismatch reported at def bad_svar_swap), not at an
# import or a syntax error.
# The C2 mutant this kills (COUPLING_LAWS_DESIGN.md section 4): svar
# and tcvar SWAPPED in the read.  A (wrong) implementation that reads
# cvar index tcvar(p) -- instead of the SOURCE cvar svar(p) -- of the
# source lane's plane passes every bounds check (mc_ok's is_lt
# conjuncts only bound the indices against the model cvar counts, and
# both indices are < 2 here) yet feeds the coupling pass the wrong
# cvar's tape.  C2's law edge_cells_cvar pins that the routed range is
# read over the source cvar's tape; this claim would let the swapped
# read silently stand in for the cvar-selective read.
# Expected failure: the two sides reduce to DIFFERENT cell lists -- the
# correct read {3.0} (cvar 0's tape at tick 2) vs the swapped read
# {6.0} (cvar 1's tape at tick 2) on the pinned 2-cvar plane -- so
# {==} cannot close.
import Base
import ../coupling.bend as C
import ../mconfig.bend as M
import ../router.bend as R

# the mutated read: the routed window over cvar index tcvar(p) of the
# SOURCE lane's plane (the svar/tcvar swap)
def edge_cells_cvar_swap(+ls: List<&2, R.Lane>, +p: M.MProj, +d: Nat, +w: Nat,
                         +tapes: List<&2, List<&2, List<&2, F32>>>, +ic: F32)
    -> List<&2, F32>:
  C.win_cells(C.cvar_tape(tapes, M.mproj_src(p), M.mproj_tcvar(p)),
              R.win_lo(R.route_window(R.lane_newest(R.nth_lane(ls, M.mproj_src(p))),
                                      d, w)),
              w, ic)

def bad_svar_swap()
  -> {C.edge_cells_cvar(R.Lane{1n, 0n, 3n} <> Nil{},
                        M.MProj{0n, 1n, 0n, 1n}, 1n, 1n,
                        ((1.0 <> 2.0 <> 3.0 <> Nil{})
                          <> (4.0 <> 5.0 <> 6.0 <> Nil{})
                          <> Nil{})
                          <> ((7.0 <> Nil{}) <> Nil{}) <> Nil{},
                        0.0)
        == edge_cells_cvar_swap(R.Lane{1n, 0n, 3n} <> Nil{},
                                M.MProj{0n, 1n, 0n, 1n}, 1n, 1n,
                                ((1.0 <> 2.0 <> 3.0 <> Nil{})
                                  <> (4.0 <> 5.0 <> 6.0 <> Nil{})
                                  <> Nil{})
                                  <> ((7.0 <> Nil{}) <> Nil{}) <> Nil{},
                                0.0)
      : List<&2, F32>}:
  {==}
