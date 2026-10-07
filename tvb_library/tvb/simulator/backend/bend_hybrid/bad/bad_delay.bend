# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The delay guard's negative: the getting-started network with per-lane
# dt 0.1 ms (scaled 100) and a 0.04 ms coupling delay (scaled 40; the
# nominal x1e6-scaled pair would be 100000 / 40000 -- instances stay
# small to fit the kernel verdict reduction budgets, the RATIO 0.4 is
# what the rule pins).
# The conversion rounds 0.04/0.1 = 0.4 ratios to **0 source steps**
# (round-half-even, the pinned rule), so md_ok's step-coverage conjunct
# computes is_ge(0, 1) = False and the whole conjunction is False.  This
# is exactly the claim a missing delay-unit guard would let through: a
# nonzero delay silently collapsing onto the zero-step read, merging two
# distinct causalities onto one line (SWEEP_LAWS_DESIGN.md gap item 6,
# "off-by-rounding shifts causality silently").  (Expected failure:
# {md_ok(...) == True} cannot close -- False vs True.)
import Base
import ../mconfig.bend as M
import ../router.bend as R

def bad_delay()
  -> {M.md_ok(100n <> 100n <> Nil{},
              40n <> Nil{},
              R.Config{1n <> 1n <> Nil{},
                       R.Proj{0n, 1n, 0n, 0n, 0n} <> Nil{},
                       1n})
       == True{} : Bool}:
  {==}
