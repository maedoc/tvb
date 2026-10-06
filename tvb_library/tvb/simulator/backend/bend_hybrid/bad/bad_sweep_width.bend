# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The fan8_exact claim WITHOUT the width witness: "the 9-sweep's lane 8 is
# covered by the 8-wide fan".  n_sweep = 9 > 8 is exactly montbrio_sweep's
# silent-drop failure mode: the fixed 8-wide fan has no lane 8, so the
# fan's lane-8 read answers "" (the default-read convention) while the
# run table's word 8 is a real sim's run -- the claim is FALSE, and it is
# exactly the claim a missing width bound would let through.  Expected
# failure: {==} cannot close ("" vs the run's non-empty string).
import Base
import ../sweep.bend as S

def bad_sweep_width(runs: List<&2, String>)
  -> {S.str_nth(S.fan8(9n, runs), 8n) == S.str_nth(runs, 8n) : String}:
  {==}
