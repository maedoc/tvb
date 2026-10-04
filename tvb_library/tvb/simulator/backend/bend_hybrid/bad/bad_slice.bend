# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# slice_nth WITHOUT the row-width witness: past the row's width the
# slice saturates to 0 (default-past-end) while the flat read still
# returns a real row, so the claim is FALSE at i = hi - lo. Expected
# failure: {==} cannot close (0 == the real row's source).
import ../router.bend as R

def bad_slice(xs: List<&2, Nat>, lo: Nat, hi: Nat)
  -> {R.nats_nth(R.nats_slice(xs, lo, hi), Nat.sub(hi, lo))
    == R.nats_nth(xs, hi) : Nat}:
  {==}
