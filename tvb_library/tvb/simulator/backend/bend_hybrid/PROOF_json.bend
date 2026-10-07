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

# False is not True: the motive sends True to Empty, so transporting along a
# proof of {False == True} lands in Empty and anything follows.
def Bool.mot(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def Bool.fne(-A: Type, e: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, (%e : Bool.mot(_)
  Unit{}))

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
# --------------------------------------------------------------------------
# 3. the ok-conditioned freshness capstone (json_read_fresh)
# --------------------------------------------------------------------------


# n <= n, Bool form
def le_refl_here(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_refl_here(p)


# a <= b implies a <= 1 + b
# (PROOF_router's filled Laws.le_succ_of_le_b, inline: filled laws do not
# re-export through module imports)
def le_succ_of_le_here(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool})
    -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Bool.fne({Nat.is_le(1n+p, 1n+0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      le_succ_of_le_here(p, q, h)

# n - anything <= n (PROOF_router's filled Laws.sub_le_b, inline)
def sub_le_here(n: Nat, d: Nat)
    -> {Nat.is_le(Nat.sub(n, d), n) == True{} : Bool}:
  match n d:
    case 0n _:
      {==}
    case 1n+p 0n:
      le_refl_here(p)
    case 1n++p 1n++q:
      le_succ_of_le_here(Nat.sub(p, q), p, sub_le_here(p, q))

# the leaf: one routed line is fresh.  route_bump reads at delay
# 1 + newest + e, so route_read's d>=1 branch gives i1 = sub(n, n+e) and
# freshness is sub_le (n - anything <= n) at the lane's newest n.
def bump_fresh(+ls: List<&2, R.Lane>, +p: R.Proj, +e: Nat)
    -> {J.line_fresh(ls, J.route_bump(ls, p, e), R.proj_src(p)) == True{} : Bool}:
  sub_le_here(R.lane_newest(R.nth_lane(ls, R.proj_src(p))),
              Nat.add(R.lane_newest(R.nth_lane(ls, R.proj_src(p))), e))

# both conjuncts hold: the and-intro counterpart of PROOF_router's
# and_elim_l/r (filled laws do not re-export, so inline)
def and_intro(a: Bool, b: Bool,
              +ha: {a == True{} : Bool},
              +hb: {b == True{} : Bool})
    -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      Bool.fne({Bool.and(False{}, b) == True{} : Bool}, ha)

# the fold: pointwise freshness over the projection list, mirroring the
# runtime predicate's own recursion so each cons needs only the leaf
# plus the induction hypothesis
def bumps_fresh(+ls: List<&2, R.Lane>, ps: List<&2, R.Proj>, +e: Nat)
    -> {J.bumps_fresh(ls, ps, e) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +h <> +t:
      and_intro(J.line_fresh(ls, J.route_bump(ls, h, e), R.proj_src(h)),
               J.bumps_fresh(ls, t, e),
               bump_fresh(ls, h, e),
               bumps_fresh(ls, t, e))

# the capstone: instantiate at the decoded config of any string, under the
# validator hypothesis.  (The lookup-boundedness half -- proj_src_bounded
# from the ok family -- is carried by line_fresh's statement: freshness
# is against nth_lane's saturating default, which is fresh too.)
def Laws.json_read_fresh(s, m, h):
  bumps_fresh(J.lanes_run(m, R.init_lanes(R.cfg_lanes(J.json_decode(s)))),
              R.cfg_projs(J.json_decode(s)), 0n)

# 3. instance laws: both sides compute
# --------------------------------------------------------------------------

def Laws.json_decode_instance():
  {==}

def Laws.json_decode_garbage():
  {==}

# --------------------------------------------------------------------------
# 4. the coupling-function spec proofs
# --------------------------------------------------------------------------

# and-elimination, both halves (PROOF_router's filled Laws.and_elim_l/r,
# inlined: filled laws do not re-export through module imports)
def and_elim_l_go(a: Bool, b: Bool, +h: {Bool.and(a, b) == True{} : Bool})
    -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Bool.fne({False{} == True{} : Bool}, h)

def and_elim_r_go(a: Bool, b: Bool, +h: {Bool.and(a, b) == True{} : Bool})
    -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Bool.fne({b == True{} : Bool}, h)

# the instance laws: both sides compute to the same normal form
def Laws.cfun_table_linear(): {==}
def Laws.cfun_table_scaling(): {==}
def Laws.cfun_table_sigmoidal(): {==}
def Laws.cfun_table_sigmoidal_jr(): {==}
def Laws.cfun_table_sigmoidal_jr_legacy(): {==}
def Laws.cfun_table_tanh(): {==}
def Laws.cfun_table_difference(): {==}
def Laws.cfun_table_kuramoto(): {==}
def Laws.cfun_table_pre_sigmoidal(): {==}
def Laws.cfun_table_pre_sigmoidal_dynamic(): {==}
def Laws.cfun_table_kuramoto_norm(): {==}
def Laws.cfun_name_linear(): {==}
def Laws.cfun_kind_unknown(): {==}
def Laws.cfun_order_linear(): {==}
def Laws.cfun_order_scaling(): {==}
def Laws.cfun_order_sigmoidal(): {==}
def Laws.cfun_order_sigmoidal_jr(): {==}
def Laws.cfun_order_sigmoidal_jr_legacy(): {==}
def Laws.cfun_order_tanh(): {==}
def Laws.cfun_order_difference(): {==}
def Laws.cfun_order_kuramoto(): {==}
def Laws.cfun_order_pre_sigmoidal(): {==}
def Laws.cfun_order_pre_sigmoidal_dynamic(): {==}
def Laws.cfun_order_kuramoto_norm(): {==}
def Laws.cf_ok_good(): {==}
def Laws.cf_ok_len_wrong(): {==}
def Laws.cf_ok_kind_unknown(): {==}
def Laws.cf_ok_junk(): {==}

# the validator's and-eliminations: cf_ok is
# and(is_lt(kind,11), and(is_eq(plen,nparams), valid)), so each conjunct
# comes off its side of the nested and
def Laws.cf_ok_in_table(c, h):
  and_elim_l_go(Nat.is_lt(J.c_kind(c), 11n),
                Bool.and(Nat.is_eq(J.c_plen(c), J.c_nparams(c)), J.c_valid(c)),
                h)

def Laws.cf_ok_len_matches(c, h):
  and_elim_l_go(Nat.is_eq(J.c_plen(c), J.c_nparams(c)), J.c_valid(c),
                and_elim_r_go(Nat.is_lt(J.c_kind(c), 11n),
                              Bool.and(Nat.is_eq(J.c_plen(c), J.c_nparams(c)),
                                       J.c_valid(c)),
                              h))

def Laws.cf_ok_parse_valid(c, h):
  and_elim_r_go(Nat.is_eq(J.c_plen(c), J.c_nparams(c)), J.c_valid(c),
                and_elim_r_go(Nat.is_lt(J.c_kind(c), 11n),
                              Bool.and(Nat.is_eq(J.c_plen(c), J.c_nparams(c)),
                                       J.c_valid(c)),
                              h))

# the capstone: the three conjuncts off the validator hypothesis, then
# reassembled into the pair equality (three cong steps under one
# Equal.trans, exactly the json_named_contract shape)
def Laws.json_cfun_contract(s, h):
  +c = J.cfun_decode(s)
  +hk = and_elim_l_go(Nat.is_lt(J.c_kind(c), 11n),
                      Bool.and(Nat.is_eq(J.c_plen(c), J.c_nparams(c)), J.c_valid(c)),
                      h)
  +h2 = and_elim_r_go(Nat.is_lt(J.c_kind(c), 11n),
                      Bool.and(Nat.is_eq(J.c_plen(c), J.c_nparams(c)), J.c_valid(c)),
                      h)
  +hl = and_elim_l_go(Nat.is_eq(J.c_plen(c), J.c_nparams(c)), J.c_valid(c), h2)
  +hv = and_elim_r_go(Nat.is_eq(J.c_plen(c), J.c_nparams(c)), J.c_valid(c), h2)
  Equal.trans(Bool & (Bool & Bool),
    (Nat.is_lt(J.c_kind(c), 11n),
     Nat.is_eq(J.c_plen(c), J.c_nparams(c)),
     J.c_valid(c)),
    (True{},
     Nat.is_eq(J.c_plen(c), J.c_nparams(c)),
     J.c_valid(c)),
    (True{}, True{}, True{}),
    Equal.cong(Bool, Bool & (Bool & Bool),
               x => (x,
                     Nat.is_eq(J.c_plen(c), J.c_nparams(c)),
                     J.c_valid(c)),
               Nat.is_lt(J.c_kind(c), 11n), True{}, hk),
    Equal.trans(Bool & (Bool & Bool),
      (True{},
       Nat.is_eq(J.c_plen(c), J.c_nparams(c)),
       J.c_valid(c)),
      (True{}, True{}, J.c_valid(c)),
      (True{}, True{}, True{}),
      Equal.cong(Bool, Bool & (Bool & Bool),
                 y => (True{}, y, J.c_valid(c)),
                 Nat.is_eq(J.c_plen(c), J.c_nparams(c)), True{}, hl),
      Equal.cong(Bool, Bool & (Bool & Bool),
                 z => (True{}, True{}, z),
                 J.c_valid(c), True{}, hv)))
