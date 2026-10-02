# PROOF_json.bend -- the proofs for LAWS_json.bend.  The gate:
#
#   bend PROOF_json.bend            must print ALL PROOFS CHECK
#   bend PROOF_json.bend --verdict  re-checked by the Lean-proved kernel
#
# Rewrite discipline (as in PROOF_router.bend): `%e : P` replaces the
# RIGHT-hand side of e by its left-hand side inside the goal.  To simplify
# X -> X' one therefore rewrites with the FLIPPED equation from
# Equal.sym(A, a, b, e) (e: {a == b} yields {b == a}): the flip's b is the
# term to eliminate, its a the replacement.  Motives are the goal's normal
# form with `_` marking the replaced position; matching is
# conversion-tolerant (a `J.route_bump(..)` motive position matches its
# reduced Line form).

import Base
import ./LAWS_json.bend as Laws
import ./router.bend as R
import ./json_ingest.bend as J

# --------------------------------------------------------------------------
# 0. the two subtraction bricks the plateau needs
# --------------------------------------------------------------------------

# the history is fully consumed: (n - (n + e)) == 0
def sub_self_zero(n: Nat, e: Nat) -> {Nat.sub(n, Nat.add(n, e)) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self_zero(p, e)

# one past the end: (n - (1 + n + e)) == 0
def sub_succ_self_zero(n: Nat, e: Nat) -> {Nat.sub(n, 1n+Nat.add(n, e)) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_succ_self_zero(p, e)

# --------------------------------------------------------------------------
# 1. the leaf plateau
# --------------------------------------------------------------------------

def Laws.read_saturate(n, num, den, win, e1, e2):
  %Equal.sym(Nat, Nat.sub(n, 1n+Nat.add(n, e1)), 0n, sub_succ_self_zero(n, e1)) : {R.Line{_, Nat.sub(n, Nat.add(n, e1)), num, den, win} == R.route_read(n, 1n+Nat.add(n, e2), num, den, win) : R.Line}
  %Equal.sym(Nat, Nat.sub(n, 1n+Nat.add(n, e2)), 0n, sub_succ_self_zero(n, e2)) : {R.Line{0n, Nat.sub(n, Nat.add(n, e1)), num, den, win} == R.Line{_, Nat.sub(n, Nat.add(n, e2)), num, den, win} : R.Line}
  %Equal.sym(Nat, Nat.sub(n, Nat.add(n, e1)), 0n, sub_self_zero(n, e1)) : {R.Line{0n, _, num, den, win} == R.Line{0n, Nat.sub(n, Nat.add(n, e2)), num, den, win} : R.Line}
  %Equal.sym(Nat, Nat.sub(n, Nat.add(n, e2)), 0n, sub_self_zero(n, e2)) : {R.Line{0n, 0n, num, den, win} == R.Line{0n, _, num, den, win} : R.Line}
  {==}

# --------------------------------------------------------------------------
# 2. per-projection, then the fold, then every string
# --------------------------------------------------------------------------

# one projection of ANY lane list is on the plateau: read_saturate at the
# source lane's newest/num/k and the projection's window
def bump_elem(+ls: List<&2, R.Lane>, +p: R.Proj, +e1: Nat, +e2: Nat)
    -> {J.route_bump(ls, p, e1) == J.route_bump(ls, p, e2) : R.Line}:
  Laws.read_saturate(R.lane_newest(R.nth_lane(ls, R.proj_src(p))),
                     R.lane_num(R.nth_lane(ls, R.proj_src(p))),
                     R.lane_k(R.nth_lane(ls, R.proj_src(p))),
                     R.proj_win(p), e1, e2)

def bump_plateau(+ls: List<&2, R.Lane>, ps: List<&2, R.Proj>, +e1: Nat, +e2: Nat)
    -> {J.routes_bump(ls, ps, e1) == J.routes_bump(ls, ps, e2) : List<&2, R.Line>}:
  match ps:
    case Nil{}:
      {==}
    case h <> t:
      %bump_elem(ls, h, e1, e2) : {J.route_bump(ls, h, e1) <> J.routes_bump(ls, t, e1) == _ <> J.routes_bump(ls, t, e2) : List<&2, R.Line>}
      %bump_plateau(ls, t, e1, e2) : {J.route_bump(ls, h, e1) <> J.routes_bump(ls, t, e1) == J.route_bump(ls, h, e1) <> _ : List<&2, R.Line>}
      {==}

# the ingress law: instantiate the fold at the decoded config of ANY
# string.  Note there is no case split on s and no hypothesis: the parser
# cannot produce a Config that escapes the plateau.
def Laws.json_delay_plateau(s, m, e1, e2):
  bump_plateau(J.lanes_run(m, R.init_lanes(R.cfg_lanes(J.json_decode(s)))),
               R.cfg_projs(J.json_decode(s)), e1, e2)

# --------------------------------------------------------------------------
# 3. instance laws: both sides compute
# --------------------------------------------------------------------------

def Laws.json_decode_instance():
  {==}

def Laws.json_decode_garbage():
  {==}
