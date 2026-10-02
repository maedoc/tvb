# PROOF_router.bend -- the proofs for LAWS_router.bend.  The gate:
#
#   bend PROOF_router.bend            must print ALL PROOFS CHECK
#   bend PROOF_router.bend --verdict  re-checked by the Lean-proved kernel
#
# Helpers with equality types (Bool.fne, the go-lemmas) are themselves proof
# terms, so --verdict covers them too.  Rewrite discipline: `%e : P` replaces
# the RIGHT-hand side of e by its left-hand side inside the goal, so a
# simplification X -> X' goes through Equal.sym(Nat, X', X, lemma) -- see
# bendygrad's PORTING_RULES.md rule 11.

import Base
import ./LAWS_router.bend as Laws
import ./router.bend as R
import ./kernel.bend as K

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
# 0. arithmetic helpers
# --------------------------------------------------------------------------

def Laws.sub_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.add_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def Laws.add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def Laws.le_refl_b(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Laws.le_refl_b(p)

def Laws.le_succ_b(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Laws.le_succ_b(p)

def Laws.le_succ_of_le(a, b, h):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Bool.fne({Nat.is_le(1n+p, 1n+0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      Laws.le_succ_of_le(p, q, h)

def Laws.sub_le_b(n, d):
  match n d:
    case 0n _:
      {==}
    case 1n+p 0n:
      Laws.le_refl_b(p)
    case 1n++p 1n++q:
      Laws.le_succ_of_le(Nat.sub(p, q), p, Laws.sub_le_b(p, q))

def Laws.lt_succ_b(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Laws.lt_succ_b(p)

# is_lt is transitive-ish under succession on the right
def lt_succ_of_lt(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool})
    -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Bool.fne({Nat.is_lt(1n+p, 1n+0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      lt_succ_of_lt(p, q, h)

# a+1 < b  implies  a < b
def lt_weaken(a: Nat, b: Nat, +h: {Nat.is_lt(1n+a, b) == True{} : Bool})
    -> {Nat.is_lt(a, b) == True{} : Bool}:
  match b:
    case 0n:
      Bool.fne({Nat.is_lt(a, 0n) == True{} : Bool}, h)
    case 1n+q:
      lt_succ_of_lt(a, q, h)

# k >= 1  implies  k-1 < k   (the k = 0 case dies on its hypothesis)
def sub_pred_lt(k: Nat, +h: {Nat.is_ge(k, 1n) == True{} : Bool})
    -> {Nat.is_lt(Nat.sub(k, 1n), k) == True{} : Bool}:
  match k:
    case 0n:
      Bool.fne({Nat.is_lt(Nat.sub(0n, 1n), 0n) == True{} : Bool}, h)
    case 1n++q:
      %Equal.sym(Nat, Nat.sub(q, 0n), q, Laws.sub_zero(q)) : {Nat.is_lt(_, 1n+q) == True{} : Bool}
      Laws.lt_succ_b(q)

def lt_zero_ge_go(q: Nat) -> {Nat.is_ge(1n+q, 1n) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

# from 0 < k (as is_lt(0, k)) extract is_ge(k, 1)
def lt_zero_is_ge(k: Nat, +h: {Nat.is_lt(0n, k) == True{} : Bool})
    -> {Nat.is_ge(k, 1n) == True{} : Bool}:
  match k:
    case 0n:
      Bool.fne({Nat.is_ge(0n, 1n) == True{} : Bool}, h)
    case 1n+q:
      lt_zero_ge_go(q)


def Laws.add_one(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_one(p) : {1n+Nat.add(p, 1n) == 1n+_ : Nat}
      {==}

def Laws.add_sub_succ(k, h):
  match k:
    case 0n:
      Bool.fne({Nat.add(Nat.sub(0n, 1n), 1n) == 0n : Nat}, h)
    case 1n++q:
      %Equal.sym(Nat, Nat.sub(q, 0n), q, Laws.sub_zero(q)) : {Nat.add(_, 1n) == 1n+q : Nat}
      Laws.add_one(q)

def Laws.eq_refl_b(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Laws.eq_refl_b(p)

def Laws.ne_succ(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Laws.ne_succ(p)

# --------------------------------------------------------------------------
# 1. the schedule
# --------------------------------------------------------------------------

def Laws.lane_newest_k1(t, n):
  match t:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, R.lane_newest(R.steps(p, R.Lane{1n, 0n, 1n+n})), Nat.add(p, 1n+n), Laws.lane_newest_k1(p, 1n+n)) : {_ == Nat.add(1n+p, n) : Nat}
      %Equal.sym(Nat, Nat.add(p, 1n+n), 1n+Nat.add(p, n), Laws.add_succ(p, n)) : {_ == Nat.add(1n+p, n) : Nat}
      {==}

# step_go keeps k, split out because a def gets one match
def k_pres_go(left: Nat, +k: Nat, +n: Nat)
    -> {R.lane_k(R.step_go(left, R.Lane{k, left, n})) == R.lane_k(R.Lane{k, left, n}) : Nat}:
  match left:
    case 0n:
      {==}
    case 1n+q:
      {==}

def Laws.lane_k_preserved(l):
  match l:
    case R.Lane{k, left, newest}:
      k_pres_go(left, k, newest)

def monotone_go(left: Nat, +k: Nat, +n: Nat)
    -> {Nat.is_le(n, R.lane_newest(R.step_go(left, R.Lane{k, left, n}))) == True{} : Bool}:
  match left:
    case 0n:
      Laws.le_succ_b(n)
    case 1n+q:
      Laws.le_refl_b(n)

def Laws.lane_monotone(l):
  match l:
    case R.Lane{k, left, newest}:
      monotone_go(left, k, newest)

# the phase invariant, step case split by the countdown
def step_preserves_go(left: Nat, +k: Nat, +n: Nat,
                      +h: {Nat.is_lt(left, k) == True{} : Bool})
    -> {Nat.is_lt(R.lane_left(R.step_go(left, R.Lane{k, left, n})), R.lane_k(R.step_go(left, R.Lane{k, left, n}))) == True{} : Bool}:
  match left:
    case 0n:
      sub_pred_lt(k, lt_zero_is_ge(k, h))
    case 1n+r:
      lt_weaken(r, k, h)

def step_preserves(+l: R.Lane,
                   +h: {Nat.is_lt(R.lane_left(l), R.lane_k(l)) == True{} : Bool})
    -> {Nat.is_lt(R.lane_left(R.step_lane(l)), R.lane_k(R.step_lane(l))) == True{} : Bool}:
  match l:
    case R.Lane{k, left, newest}:
      step_preserves_go(left, k, newest, h)

def Laws.lane_phase_bound(t, l, h):
  match t:
    case 0n:
      h
    case 1n+p:
      %Laws.lane_k_preserved(l) : {Nat.is_lt(R.lane_left(R.steps(p, R.step_lane(l))), _) == True{} : Bool}
      Laws.lane_phase_bound(p, R.step_lane(l), step_preserves(l, h))


def left_det_go(left: Nat, +k: Nat, +n: Nat)
    -> {R.lane_left(R.step_go(left, R.Lane{k, left, n})) == R.left_next(left, k) : Nat}:
  match left:
    case 0n:
      {==}
    case 1n+r:
      {==}

def Laws.left_det(l):
  match l:
    case R.Lane{k, left, newest}:
      left_det_go(left, k, newest)

def Laws.sub_add_cancel(n, d, h):
  match n d:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Bool.fne({Nat.add(Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, h)
    case 1n+p 0n:
      %Laws.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), Laws.add_succ(Nat.sub(p, q), q)) : {_ == 1n+p : Nat}
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), q), p, Laws.sub_add_cancel(p, q, h)) : {1n+_ == 1n+p : Nat}
      {==}

# --------------------------------------------------------------------------
# 1b. control flow
# --------------------------------------------------------------------------

def hold_go(left: Nat, +k: Nat, +n: Nat, +h: {Nat.is_ne(left, 0n) == True{} : Bool})
    -> {R.lane_newest(R.step_go(left, R.Lane{k, left, n})) == n : Nat}:
  match left:
    case 0n:
      Bool.fne({R.lane_newest(R.step_go(0n, R.Lane{k, 0n, n})) == n : Nat}, h)
    case 1n+r:
      {==}

def Laws.lane_hold(l, h):
  match l:
    case R.Lane{k, left, newest}:
      hold_go(left, k, newest, h)

def due_go(left: Nat, +k: Nat, +n: Nat, +h: {Nat.is_eq(left, 0n) == True{} : Bool})
    -> {R.lane_newest(R.step_go(left, R.Lane{k, left, n})) == 1n+n : Nat}:
  match left:
    case 0n:
      {==}
    case 1n+r:
      Bool.fne({R.lane_newest(R.step_go(1n+r, R.Lane{k, 1n+r, n})) == 1n+n : Nat}, h)

def Laws.due_publishes(l, h):
  match l:
    case R.Lane{k, left, newest}:
      due_go(left, k, newest, h)

def due_iff_go(left: Nat, +k: Nat, +n: Nat)
    -> {Nat.is_eq(R.lane_newest(R.step_go(left, R.Lane{k, left, n})), 1n+n) == Nat.is_eq(left, 0n) : Bool}:
  match left:
    case 0n:
      Laws.eq_refl_b(n)
    case 1n+r:
      Laws.ne_succ(n)

def Laws.due_iff_publishes(l):
  match l:
    case R.Lane{k, left, newest}:
      due_iff_go(left, k, newest)

def Laws.run_segmentable(a, b, l):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Laws.run_segmentable(p, b, R.step_lane(l))

def Laws.countdown_publish(left, k, n):
  match left:
    case 0n:
      {==}
    case 1n+r:
      Laws.countdown_publish(r, k, n)

def Laws.period_from_init(k, n, h):
  %Laws.add_sub_succ(k, h) : {R.steps(_, R.Lane{k, Nat.sub(k, 1n), n}) == R.Lane{k, Nat.sub(k, 1n), 1n+n} : R.Lane}
  Laws.countdown_publish(Nat.sub(k, 1n), k, n)

# --------------------------------------------------------------------------
# 2. the read
# --------------------------------------------------------------------------

def Laws.read_fresh(n, d, num, den, win):
  match d:
    case 0n:
      Laws.le_refl_b(n)
    case 1n+dp:
      Laws.sub_le_b(n, dp)

def Laws.clamp_necessary(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Laws.clamp_necessary(p)

def Laws.delay_shift(n, d):
  %Equal.sym(Nat, Nat.sub(n, 0n), n, Laws.sub_zero(n)) : {Nat.sub(n, d) == Nat.sub(_, d) : Nat}
  {==}

# the k=1 counter law specialised to a zero start: newest == t
def newest_k1_t(+t: Nat) -> {R.lane_newest(R.steps(t, R.Lane{1n, 0n, 0n})) == t : Nat}:
  Equal.trans(Nat, R.lane_newest(R.steps(t, R.Lane{1n, 0n, 0n})), Nat.add(t, 0n), t,
              Laws.lane_newest_k1(t, 0n), Laws.add_zero(t))

def Laws.degenerate_read(t, d):
  match d:
    case 0n:
      %Equal.sym(Nat, R.lane_newest(R.steps(t, R.Lane{1n, 0n, 0n})), t, newest_k1_t(t)) : {_ == Nat.sub(t, 0n) : Nat}
      %Equal.sym(Nat, Nat.sub(t, 0n), t, Laws.sub_zero(t)) : {t == _ : Nat}
      {==}
    case 1n++dp:
      %Equal.sym(Nat, R.lane_newest(R.steps(t, R.Lane{1n, 0n, 0n})), t, newest_k1_t(t)) : {Nat.sub(_, 1n+dp) == Nat.sub(t, 1n+dp) : Nat}
      {==}

# --------------------------------------------------------------------------
# 3. the configuration tree -- all concrete, all by normalisation
# --------------------------------------------------------------------------

def Laws.ok_good():
  {==}

def Laws.ok_bad_period():
  {==}

def Laws.ok_bad_delay():
  {==}

def Laws.ok_bad_clash():
  {==}

def Laws.window_instance():
  {==}

# --------------------------------------------------------------------------
# 3b. the CSR data structure -- all concrete, all by normalisation
# --------------------------------------------------------------------------

def Laws.csr_ok_good():
  {==}

def Laws.csr_ok_bad_count():
  {==}

def Laws.csr_ok_bad_unordered():
  {==}

def Laws.csr_ok_bad_index():
  {==}

def Laws.csr_ok_bad_delay():
  {==}

# --------------------------------------------------------------------------
# 4. the leaf layer -- all definitional: both sides are the same term
# --------------------------------------------------------------------------

def Laws.blend_order(x0, x1, a):
  {==}

def Laws.cfun_linear_order(a, b, w):
  {==}

def Laws.gather_nil(acc):
  {==}

def Laws.gather_cons(e, t, acc):
  {==}
