# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# blend_adjacent WITHOUT the in-history witness: at n = 0, d = 1 the
# saturating sub collapses both endpoints to 0n, so the routed line's
# endpoints are NOT one tick apart -- the claim is false and the
# witness le_ok(1n+dp, n) is load-bearing. Expected failure: {==}
# cannot close (l_i1 == l_i0 + 1 is 0 == 1 at n = 0).
import ../router.bend as R

def bad_blend_adj(num: Nat, den: Nat, win: Nat)
  -> {R.l_i1(R.route_read(0n, 1n, num, den, win))
    == Nat.add(R.l_i0(R.route_read(0n, 1n, num, den, win)), 1n) : Nat}:
  {==}
