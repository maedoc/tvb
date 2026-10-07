# NEGATIVE CONTROL -- this file MUST NOT typecheck, and it MUST fail AT
# ITS CLAIM (a {==} mismatch reported at def bad_cvar_wrong_inrange),
# not at an import or a syntax error.
# The hole bad/bad_cvar.bend leaves, stated as a stage-A claim
# (COUPLING_LAWS_DESIGN.md section 2.6 and section 4): bad_cvar.bend
# catches an OUT-OF-RANGE source cvar (the mc_ok bounds conjunct
# is_lt(svar, shapes[src]) computes False); a WRONG-BUT-IN-RANGE source
# cvar -- both 0n and 1n are < the source lane's cvar count 2n -- passes
# every bounds check yet routes the coupling pass a DIFFERENT cvar's
# tape.  C2's law edge_cells_cvar makes svar load-bearing in the READ:
# this claim asserts the wrong cvar's routed range IS the right cvar's.
# Expected failure: the two sides reduce to DIFFERENT cell lists ({3.0}
# for svar 0's tape vs {6.0} for svar 1's tape at the same routed tick),
# so {==} cannot close -- the bounds check would NOT have caught it.
import Base
import ../coupling.bend as C
import ../mconfig.bend as M
import ../router.bend as R

def bad_cvar_wrong_inrange()
  -> {C.edge_cells_cvar(R.Lane{1n, 0n, 3n} <> Nil{},
                        M.MProj{0n, 1n, 0n, 0n}, 1n, 1n,
                        ((1.0 <> 2.0 <> 3.0 <> Nil{})
                          <> (4.0 <> 5.0 <> 6.0 <> Nil{})
                          <> Nil{})
                          <> ((7.0 <> Nil{}) <> Nil{}) <> Nil{},
                        0.0)
        == C.edge_cells_cvar(R.Lane{1n, 0n, 3n} <> Nil{},
                             M.MProj{0n, 1n, 1n, 0n}, 1n, 1n,
                             ((1.0 <> 2.0 <> 3.0 <> Nil{})
                               <> (4.0 <> 5.0 <> 6.0 <> Nil{})
                               <> Nil{})
                               <> ((7.0 <> Nil{}) <> Nil{}) <> Nil{},
                             0.0)
      : List<&2, F32>}:
  {==}
