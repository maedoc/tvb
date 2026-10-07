# Functional smoke test for mconfig.bend: the getting-started
# heterogeneous network (cortex cvar count 2, thalamus cvar count 1,
# one cross-model projection).  Pins the view constructor (one MProj
# per projection, src/tgt copied), the model-relative cvar bounds
# (svar 0 < 2, tcvar 0 < 1), the validator's verdict on the good
# and the bad-cvar (target cvar 1 of a 1-cvar model) shape, and the
# P4 name resolution: 'y1' -> 1 on JansenRit, 'xi' -> 0 on FHN but
# junk (the name list's length, 6) on JansenRit, and the named view
# (resolved svar 1, tcvar 0) accepted by mc_ok against the 6/4
# state-variable counts.
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
  +jr_names : List<&2, String> = {"y0" <> "y1" <> "y2" <> "y3" <> "y4" <> "y5" <> Nil{} : List<&2, String>}
  +fhn_names : List<&2, String> = {"xi" <> "eta" <> "alpha" <> "beta" <> Nil{} : List<&2, String>}
  +models : List<&2, List<&2, String>> = {jr_names <> fhn_names <> Nil{} : List<&2, List<&2, String>>}
  +namedok : Bool = M.mc_ok({6n <> 4n <> Nil{} : List<&2, Nat>},
                            M.mnview(M.NProj{0n, 1n, "y1", "xi"} <> Nil{}, models), c)
  +jrslot : Nat = M.find_name(jr_names, "y1")
  +jrxi : Nat = M.find_name(jr_names, "xi")
  +fhnxi : Nat = M.find_name(fhn_names, "xi")
  +out : String = " " ++ Bool.show(M.mc_ok(shapes, mps, c)) ++ "\n"
    ++ " " ++ Bool.show(M.mc_ok(shapes, bad, c)) ++ "\n"
    ++ " " ++ Bool.show(lenok) ++ "\n"
    ++ " " ++ Bool.show(srcpair) ++ "\n"
    ++ " " ++ Bool.show(svin) ++ "\n"
    ++ " " ++ Bool.show(tvin) ++ "\n"
    ++ " " ++ Bool.show(namedok) ++ "\n"
    ++ " " ++ Nat.show(jrslot) ++ "\n"
    ++ " " ++ Nat.show(jrxi) ++ "\n"
    ++ " " ++ Nat.show(fhnxi) ++ "\n"
  do IO<Unit>:
    IO.print(out)

#| True
#| False
#| True
#| True
#| True
#| True
#| True
#| 1
#| 6
#| 0
