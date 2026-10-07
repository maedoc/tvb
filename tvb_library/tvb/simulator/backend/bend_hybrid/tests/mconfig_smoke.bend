# Functional smoke test for mconfig.bend: the getting-started
# heterogeneous network (cortex cvar count 2, thalamus cvar count 1,
# one cross-model projection).  Pins the view constructor (one MProj
# per projection, src/tgt copied), the model-relative cvar bounds
# (svar 0 < 2, tcvar 0 < 1), and the validator's verdict on the good
# and the bad-cvar (target cvar 1 of a 1-cvar model) shape.
# Expected lines are pinned below (#|); run via tests/run_mconfig.sh.
import Base
import ../mconfig.bend as M
import ../router.bend as R

def main() -> IO(Unit):
  +c : R.Config = R.Config{1n <> 1n <> Nil{}, R.Proj{0n, 1n, 0n, 0n, 0n} <> Nil{}, 1n}
  +shapes : List<&2, Nat> = {2n <> 1n <> Nil{} : List<&2, Nat>}
  +svs : List<&2, Nat> = {0n <> Nil{} : List<&2, Nat>}
  +mps : List<&2, M.MProj> = M.mview(R.cfg_projs(c), svs, svs)
  +bad : List<&2, M.MProj> = M.mview(R.cfg_projs(c), svs, {1n <> Nil{} : List<&2, Nat>})
  +lenok : Bool = Nat.is_eq(M.mprojs_len(mps), R.projs_len(R.cfg_projs(c)))
  +srcpair : Bool = Nat.is_eq(M.mproj_src(M.nth_mproj(mps, 0n)),
                              R.proj_src(R.nth_proj(R.cfg_projs(c), 0n)))
  +svin : Bool = Nat.is_lt(M.mproj_svar(M.nth_mproj(mps, 0n)), 2n)
  +tvin : Bool = Nat.is_lt(M.mproj_tcvar(M.nth_mproj(mps, 0n)), 1n)
  +out : String = " " ++ Bool.show(M.mc_ok(shapes, mps, c)) ++ "\n"
    ++ " " ++ Bool.show(M.mc_ok(shapes, bad, c)) ++ "\n"
    ++ " " ++ Bool.show(lenok) ++ "\n"
    ++ " " ++ Bool.show(srcpair) ++ "\n"
    ++ " " ++ Bool.show(svin) ++ "\n"
    ++ " " ++ Bool.show(tvin) ++ "\n"
  do IO<Unit>:
    IO.print(out)

#| True
#| False
#| True
#| True
#| True
#| True
