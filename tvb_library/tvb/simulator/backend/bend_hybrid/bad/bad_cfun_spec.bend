# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The cfun config-spec must be punctuation-proof in three places; each
# claim below transcribes the reference WRONG and must fail at its own
# claim def (not at an import):
#   1. bad_cfun_swap      -- JSON cfun_params[i] lands in field i.  The
#      claim decodes [3,5] as a=5,b=3 (the fields swapped); the decoder
#      gives a=3,b=5, so the normal forms differ.
#   2. bad_cfun_mistag    -- kuramoto is PRE (per-edge sin before the
#      weighted sum); the claim tags it post (pre=False).  A mis-tag is
#      silently wrong (sum-of-sins vs sin-of-sum), so it must be
#      unstatable.
#   3. bad_cfun_wronglen  -- cf_ok rejects a params length that does not
#      match the kind's table count (linear takes exactly 2); the claim
#      asserts 3 is accepted.
import Base
import ../json_ingest.bend as J

def bad_cfun_swap()
    -> {J.cfun_decode("{\"cfun_kind\":\"linear\",\"cfun_params\":[3,5]}")
          == J.CFun{0n, False{}, 1n, 5n, 3n, 0n, 0n, 0n, 0n, 2n, 2n, True{}} : J.CFun}:
  {==}

def bad_cfun_mistag()
    -> {J.cfun_decode("{\"cfun_kind\":\"kuramoto\",\"cfun_params\":[]}")
          == J.CFun{7n, False{}, 2n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, True{}} : J.CFun}:
  {==}

def bad_cfun_wronglen()
    -> {J.cf_ok(J.cfun_decode("{\"cfun_kind\":\"linear\",\"cfun_params\":[1,2,3]}")) == True{} : Bool}:
  {==}
