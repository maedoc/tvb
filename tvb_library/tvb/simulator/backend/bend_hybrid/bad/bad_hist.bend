# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# A concrete falsity witness for hist_snoc_stable WITHOUT the lt_ok
# bound: read at the OLD length after a snoc -- the position the snoc
# just filled.  The unwitnessed claim says the read there is unchanged
# (the old IC answer), but the tape now holds v there: term inequality
# 2.5 == 0.0 is not provable (floats are opaque), so the claim fails.
# This is exactly the off-by-one the lt_ok(i, hist_len) witness exists
# to exclude: "appending changes nothing below the top" is true, and
# "appending changes nothing AT the top" is false -- the top is the
# write.
import Base
import ../hist.bend as H

def bad_hist()
    -> {H.hist_read(H.hist_snoc(Nil{}, 2.5), 0n, 0.0) == 0.0 : F32}:
  {==}
