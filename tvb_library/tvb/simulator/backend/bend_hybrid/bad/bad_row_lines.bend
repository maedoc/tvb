# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# row_lines_nth WITHOUT the row-width witness: past the row's width the
# routing table saturates to the default Line while the config's flat
# read still returns a real edge -- the claim is FALSE at j = hi - lo.
# Expected failure: {==} cannot close (default Line vs the real edge).
import ../router.bend as R

def bad_row_lines(ls: List<&2, R.Lane>, +c: R.Csr, +t: Nat)
  -> {R.nth_line(R.csr_row_lines(ls, c, t),
                 Nat.sub(R.csr_row_hi(c, t), R.csr_row_lo(c, t)))
    == R.edge(ls,
        R.nats_nth(R.csr_indices(c), R.csr_row_hi(c, t)),
        R.nats_nth(R.csr_delays(c), R.csr_row_hi(c, t)))
    : R.Line}:
  {==}
