# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The plateau is across DELAYS at a fixed tick, NOT across ticks: the
# interpolating fraction num = k-1-left keeps moving between a slow lane's
# publications, so the saturated read CHANGES from tick to tick (that is
# the ZOH staircase).  This claims tick-invariance for one concrete JSON
# config, and must fail: run_bump at m=3 is Line{0n, 0n, 1n, 2n, 0n} and
# at m=4 is Line{0n, 0n, 0n, 2n, 0n} (the k=2 source's phase flipped).
# If this proof were accepted, the statement of json_delay_plateau would
# be misunderstood -- and it is not what is proved.
import Base
import ../router.bend as R
import ../json_ingest.bend as J

def bad_json_time()
    -> {J.run_bump(J.json_decode("{\"lanes\":[1,2],\"projs\":[[1,0,1,0,0]],\"horizon\":4}"), 3n, 0n)
          == J.run_bump(J.json_decode("{\"lanes\":[1,2],\"projs\":[[1,0,1,0,0]],\"horizon\":4}"), 4n, 0n)
             : List<&2, R.Line>}:
  {==}
