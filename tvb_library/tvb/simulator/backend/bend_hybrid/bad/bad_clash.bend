# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The mirror of Laws.ok_bad_clash: it claims a config with two projections
# writing the same (target, slot) is VALID.  False, so the claim must be
# REJECTED.  Expected failure: {==} cannot close {False{} == True{} : Bool}.
import Base
import ../router.bend as R

def CLASH() -> R.Config:
  R.Config{1n <> 2n <> Nil{},
           R.Proj{0n, 1n, 1n, 0n, 0n} <> R.Proj{1n, 1n, 1n, 0n, 0n} <> Nil{},
           4n}

def bad_clash_ok() -> {R.ok(CLASH()) == True{} : Bool}:
  {==}
