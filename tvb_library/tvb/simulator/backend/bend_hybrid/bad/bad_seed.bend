# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The seed validator's negative: a TWO-sim seed column with a DUPLICATED
# seed -- sims 0 and 1 both seeded 100.  seeds_unique folds
# no_seed_clash(100, [100]) = is_ne(100, 100) = False, so the whole
# validator is False.  This is exactly the claim a missing distinctness
# conjunct would let through: two sims' noise streams aliased onto ONE
# stream -- correlated Monte-Carlo samples that still look plausible.
# Expected failure: sweep_seed_ok computes to False, so {False == True}
# cannot close.
import Base
import ../sweep.bend as S
import ../router.bend as R

def bad_seed()
  -> {S.sweep_seed_ok(100n <> 100n <> Nil{},
                      R.Config{1n <> 2n <> Nil{},
                               R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{},
                               4n})
       == True{} : Bool}:
  {==}
