# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# A concrete falsity witness for ring_first_lap WITHOUT the lt_ok fence:
# at i = cap (one past the fence) the mod wraps to 0, so the ring read
# answers slot 0's value, not slot cap's.  On the tape [1.5, 2.5] with
# cap = 2, ring_read(i=2) = hist_read(slot mod(2,2)=0) = 1.5, but the
# fenceless claim says it equals hist_read(tape, 2, ic) = the tape's
# index-2 read = IC = 0.0 -- 1.5 == 0.0, unprovable.  This is exactly
# the second-lap aliasing the cap >= horizon config conjunct exists to
# fence off: an under-sized ring quietly returns the WRONG sample, the
# oldest one, as if it were the newest.
import Base
import ../hist.bend as H

def bad_ring()
    -> {H.ring_read({1.5 <> 2.5 <> Nil{} : List<&2, F32>}, 2n, 2n, 0.0)
        == H.hist_read({1.5 <> 2.5 <> Nil{} : List<&2, F32>}, 2n, 0.0) : F32}:
  {==}
