# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The capacity gate's falsity witness: an UNDER-CAPACITY ring (cap = 3 <
# horizon = 4) accepting a config is not just a validator failure, it
# breaks the correspondence itself.  On the tape [1.5, 2.5, 3.5] with
# cap = 3, the in-window read at absolute index i = 4 (which the
# horizon-4 window [n-4, n] at n = 4 must cover) wraps: slot 4 mod 3 = 1
# answers 2.5, while the tape answers its index-4 read, the IC fill 0.0.
# The fenceless claim "the ring read equals the tape read" is therefore
# unprovable -- exactly the aliasing ok_cap exists to fence off.  This is
# bad_ring at the config level: there the fenceless index was outside
# [0, cap); here it is INSIDE the horizon window yet outside the ring's
# single lap.
import Base
import ../hist.bend as H

def bad_cap() -> Bool:
  Bool.and(Nat.is_le(4n, 4n),          # n - horizon = 0 <= i = 4 <= n = 4
           Nat.is_le(4n, 4n))

def bad_cap_claim()
    -> {H.ring_read({1.5 <> 2.5 <> 3.5 <> Nil{} : List<&2, F32>}, 4n, 3n, 0.0)
        == H.hist_read({1.5 <> 2.5 <> 3.5 <> Nil{} : List<&2, F32>}, 4n, 0.0)
        : F32}:
  {==}
