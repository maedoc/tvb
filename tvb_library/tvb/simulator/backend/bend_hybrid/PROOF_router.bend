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
import ./hist.bend as H

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
# 1c. monitors
# --------------------------------------------------------------------------
# count_shared: the count is the master clock, independent of the lanes.
# Induction on t; mon_tick is a pure succ on the count.
def Laws.count_shared(t, ks, m):
  match t:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        R.mon_n(R.mon_ticks(p, ks, R.mon_tick(m))),
        Nat.add(p, 1n+R.mon_n(m)),
        1n+Nat.add(p, R.mon_n(m)),
        Laws.count_shared(p, ks, R.mon_tick(m)),
        Laws.add_succ(p, R.mon_n(m)))

# count_shared, init form: the count after t ticks from Mon{0} is t
def count_init(+t: Nat, +ks: List<&2, Nat>)
    -> {R.mon_n(R.mon_ticks(t, ks, R.mon_init())) == t : Nat}:
  Equal.trans(Nat, R.mon_n(R.mon_ticks(t, ks, R.mon_init())), Nat.add(t, 0n), t,
              Laws.count_shared(t, ks, R.mon_init()), Laws.add_zero(t))

def Laws.monitor_zoh_average(k, h, ks):
  count_init(k, ks)

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

# --------------------------------------------------------------------------
# 0c. the subtraction library (discharges LAWS 0b, appended)
# --------------------------------------------------------------------------

# 1n+x <= y implies x <= y (weaken the left succ)
def le_sub_succ(+x: Nat, y: Nat, +h: {Nat.is_le(1n+x, y) == True{} : Bool})
    -> {Nat.is_le(x, y) == True{} : Bool}:
  match y:
    case 0n:
      Bool.fne({Nat.is_le(x, 0n) == True{} : Bool}, h)
    case 1n++q:
      Laws.le_succ_of_le(x, q, h)

# the decider le_ok(a,b) implies the Bool test
def le_ok_iff_go(a: Nat, b: Nat, h: R.le_ok(a, b))
    -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n++p 1n++q:
      le_ok_iff_go(p, q, h)

def Laws.le_ok_iff(a, b, h):
  le_ok_iff_go(a, b, h)

def le_ok_of_b_go(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool})
    -> {(R.le_ok(a, b) : Type) == Unit : Type}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Bool.fne({(R.le_ok(1n+p, 0n) : Type) == Unit : Type}, h)
    case 1n++p 1n++q:
      le_ok_of_b_go(p, q, h)

def Laws.le_ok_of_b(a, b, h):
  le_ok_of_b_go(a, b, h)

# (n - d) - w == n - (d + w) when d + w <= n (decider form): the witness
# destructures with the triple, so the saturation cases are definitional
# and the succ case recurses structurally.
def sub_sub_add_go(n: Nat, d: Nat, w: Nat, h: R.le_ok(Nat.add(d, w), n))
    -> {Nat.sub(Nat.sub(n, d), w) == Nat.sub(n, Nat.add(d, w)) : Nat}:
  match n d:
    case 0n _:
      {==}
    case 1n++p 0n:
      {==}
    case 1n++p 1n++qd:
      sub_sub_add_go(p, qd, w, h)

def Laws.sub_sub_add(n, d, w, h):
  sub_sub_add_go(n, d, w, h)

def Laws.sub_le_self(n, d):
  match n d:
    case 0n _:
      {==}
    case 1n++p 0n:
      Laws.le_refl_b(1n+p)
    case 1n++p 1n++q:
      Laws.le_succ_of_le(Nat.sub(p, q), p, Laws.sub_le_self(p, q))

# 0 <= c, unconditionally
def le_zero(c: Nat) -> {Nat.is_le(0n, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++r:
      {==}

def le_trans_go(a: Nat, b: Nat, c: Nat,
               +h1: {Nat.is_le(a, b) == True{} : Bool},
               +h2: {Nat.is_le(b, c) == True{} : Bool})
    -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b:
    case 0n _:
      le_zero(c)
    case 1n+p 0n:
      Bool.fne({Nat.is_le(1n+p, c) == True{} : Bool}, h1)
    case 1n++p 1n++q:
      match c:
        case 0n:
          Bool.fne({Nat.is_le(1n+p, 0n) == True{} : Bool}, h2)
        case 1n++r:
          le_trans_go(p, q, r, h1, h2)

def Laws.le_trans(a, b, c, h1, h2):
  le_trans_go(a, b, c, h1, h2)

# --------------------------------------------------------------------------
# 0d. window-span bricks and the Q2 span law
# --------------------------------------------------------------------------

# n - n == 0
def Laws.sub_self(n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      Laws.sub_self(p)

# a <= 1 + a, unconditionally
def Laws.le_add_one(a):
  match a:
    case 0n:
      {==}
    case 1n++p:
      Laws.le_add_one(p)


# n - 0 == n
def Laws.sub_zero_r(n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      {==}

# (1+m) - x == 1 + (m - x) when x <= m
def sub_succ_l_go(m: Nat, x: Nat,
                  +h: {Nat.is_le(x, m) == True{} : Bool})
    -> {Nat.sub(1n+m, x) == Nat.add(1n, Nat.sub(m, x)) : Nat}:
  match m x:
    case _ 0n:
      {==}
    case 0n 1n++q:
      Bool.fne({Nat.sub(1n+0n, 1n+q) == Nat.add(1n, Nat.sub(0n, q)) : Nat}, h)
    case 1n+p 1n+q:
      sub_succ_l_go(p, q, h)

def Laws.sub_succ_l(m, x, h):
  sub_succ_l_go(m, x, h)

# m - (m - w) == w when w <= m
def sub_sub_cancel_go(m: Nat, w: Nat,
                      +h: {Nat.is_le(w, m) == True{} : Bool})
    -> {Nat.sub(m, Nat.sub(m, w)) == w : Nat}:
  match m w:
    case 0n 0n:
      {==}
    case 1n++p 0n:
      Laws.sub_self(p)
    case 0n 1n++q:
      Bool.fne({Nat.sub(0n, Nat.sub(0n, 1n+q)) == 1n+q : Nat}, h)
    case 1n++p 1n++q:
      Equal.trans(Nat,
        Nat.sub(1n+p, Nat.sub(p, q)),
        Nat.add(1n, Nat.sub(p, Nat.sub(p, q))),
        Nat.add(1n, q),
        Laws.sub_succ_l(p, Nat.sub(p, q), Laws.sub_le_self(p, q)),
        Equal.cong(Nat, Nat, z => Nat.add(1n, z),
                   Nat.sub(p, Nat.sub(p, q)), q,
                   sub_sub_cancel_go(p, q, h)))

def Laws.sub_sub_cancel(m, w, h):
  sub_sub_cancel_go(m, w, h)

# w <= n - d whenever d + w <= n (decider witness in, Bool out).  Matching
# d first makes the add inside the witness reduce; in the double-succ case
# the witness IS the recursive witness, definitionally.
def le_sub_add_go(+d: Nat, +n: Nat, +w: Nat, h: R.le_ok(Nat.add(d, w), n))
    -> {Nat.is_le(w, Nat.sub(n, d)) == True{} : Bool}:
  match d n:
    case 0n 0n:
      match w:
        case 0n:
          {==}
        case 1n+r:
          Empty.absurd({Nat.is_le(1n+r, 0n) == True{} : Bool}, h)
    case 0n 1n+p:
      Laws.le_ok_iff(w, 1n+p, h)
    case 1n++q 0n:
      Empty.absurd({Nat.is_le(w, 0n) == True{} : Bool}, h)
    case 1n++q 1n++p:
      le_sub_add_go(q, p, w, h)

def Laws.le_sub_add(n, d, w, h):
  le_sub_add_go(d, n, w, h)

# hi - lo == w, quantified: one induction consuming the witness exactly once.
# n=0 closes by absurdity (d+w <= 0 forces w=d=0 or Empty); d=0 reduces the
# goal to sub_sub_cancel on n; the double-succ case recurses with the very
# same witness, since le_ok(1+q+w, 1+p) IS le_ok(q+w, p) definitionally.
def window_span_go(+n: Nat, +d: Nat, +w: Nat, h: R.le_ok(Nat.add(d, w), n))
    -> {Nat.sub(R.win_hi(R.route_window(n, d, w)), R.win_lo(R.route_window(n, d, w))) == w : Nat}:
  match n d:
    case 0n 0n:
      match w:
        case 0n:
          {==}
        case 1n+r:
          Empty.absurd({Nat.sub(R.win_hi(R.route_window(0n, 0n, 1n+r)), R.win_lo(R.route_window(0n, 0n, 1n+r))) == 1n+r : Nat}, h)
    case 0n 1n+q:
      Empty.absurd({Nat.sub(R.win_hi(R.route_window(0n, 1n+q, w)), R.win_lo(R.route_window(0n, 1n+q, w))) == w : Nat}, h)
    case 1n+p 0n:
      Laws.sub_sub_cancel(1n+p, w, Laws.le_ok_iff(w, 1n+p, h))
    case 1n+p 1n+q:
      window_span_go(p, q, w, h)

def Laws.window_span(n, d, w, h):
  window_span_go(n, d, w, h)

# Q1 hold half: t < left+1 ticks from countdown left hold newest.  The
# induction peels ticks while the countdown is a successor, and the witness
# reduces definitionally as left shrinks; when t=0 the claim is reflexive.

# is_lt(p, 0n) is absurd for any p: once p is destructed the cmp reduces to
# GT (or EQ for 0), so the hypothesis becomes False == True; refute any goal.
def lt_zero_absurd(p: Nat, -A: Type, h: {Nat.is_lt(p, 0n) == True{} : Bool}) -> A:
  match p:
    case 0n:
      Bool.fne(A, h)
    case 1n+q:
      Bool.fne(A, h)

def hold_until_due_go(t: Nat, +k: Nat, left: Nat, +n: Nat,
                      h: {Nat.is_lt(t, Nat.add(left, 1n)) == True{} : Bool})
    -> {R.lane_newest(R.steps(t, R.Lane{k, left, n})) == n : Nat}:
  match t left:
    case 0n _:
      {==}
    case 1n+p 0n:
      lt_zero_absurd(p, {R.lane_newest(R.steps(1n+p, R.Lane{k, 0n, n})) == n : Nat}, h)
    case 1n+p 1n+q:
      hold_until_due_go(p, k, q, n, h)

def Laws.hold_until_due(t, k, left, n, h):
  hold_until_due_go(t, k, left, n, h)

# countdown stays inside [0, k-1]: left=0 resets to k-1 (trivially <= k-1);
# left=1+q steps down to q, and q <= 1+q <= k-1 by hypothesis transitivity.
def left_invariant_go(left: Nat, +k: Nat,
                      h: {Nat.is_le(left, Nat.sub(k, 1n)) == True{} : Bool})
    -> {Nat.is_le(R.left_next(left, k), Nat.sub(k, 1n)) == True{} : Bool}:
  match left:
    case 0n:
      Laws.le_refl_b(Nat.sub(k, 1n))
    case 1n+q:
      match k:
        case 0n:
          Bool.fne({Nat.is_le(R.left_next(1n+q, 0n), Nat.sub(0n, 1n)) == True{} : Bool}, h)
        case 1n+kk:
          match kk:
            case 0n:
              Bool.fne({Nat.is_le(q, 0n) == True{} : Bool}, h)
            case 1n+r:
              Laws.le_succ_of_le(q, r, h)

def Laws.left_invariant(left, k, h):
  left_invariant_go(left, k, h)

# x < y implies x != y (the ne half of lt)
def lt_imp_ne(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool})
    -> {Nat.is_ne(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Bool.fne({Nat.is_ne(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Bool.fne({Nat.is_ne(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      lt_imp_ne(p, q, h)

# x <= p implies x < 1+p (le strengthens to lt across a successor)
def le_lt_succ(x: Nat, p: Nat, h: {Nat.is_le(x, p) == True{} : Bool})
    -> {Nat.is_lt(x, 1n+p) == True{} : Bool}:
  match x p:
    case 0n _:
      {==}
    case 1n+r 0n:
      Bool.fne({Nat.is_lt(1n+r, 1n+0n) == True{} : Bool}, h)
    case 1n+r 1n+s:
      le_lt_succ(r, s, h)

# sub is strictly antitone in its second argument inside the history:
# a < b <= n implies n-b < n-a.  Induction on (n, b) with the a=0 case
# closed by sub_le_self + le_lt_succ.
def sub_lt_mono(+n: Nat, +a: Nat, +b: Nat,
               h: {Nat.is_lt(a, b) == True{} : Bool},
               hb: R.le_ok(b, n))
    -> {Nat.is_lt(Nat.sub(n, b), Nat.sub(n, a)) == True{} : Bool}:
  match n a b:
    case 0n _ 0n:
      lt_zero_absurd(a, {Nat.is_lt(Nat.sub(0n, 0n), Nat.sub(0n, a)) == True{} : Bool}, h)
    case 0n _ 1n+q:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+q), Nat.sub(0n, a)) == True{} : Bool}, hb)
    case 1n+p _ 0n:
      lt_zero_absurd(a, {Nat.is_lt(Nat.sub(1n+p, 0n), Nat.sub(1n+p, a)) == True{} : Bool}, h)
    case 1n+p 0n 1n+q:
      le_lt_succ(Nat.sub(p, q), p, Laws.sub_le_self(p, q))
    case 1n+p 1n+r 1n+q:
      sub_lt_mono(p, r, q, h, hb)

# delay injectivity: distinct delays inside the history read distinct
# samples.  Strict antitonicity (sub_lt_mono) gives n-b < n-a, and lt_imp_ne
# turns the strict order into the disequality.
# disequality is symmetric (cmp flips EQ-free to EQ-free)
def ne_symm(x: Nat, y: Nat, h: {Nat.is_ne(x, y) == True{} : Bool})
    -> {Nat.is_ne(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Bool.fne({Nat.is_ne(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ne_symm(p, q, h)


# the go half with +b (Nat is Data, so the reusable binder is legal here);
# n and a stay affine -- each is used exactly once per call below.
def delay_inj_go(+n: Nat, +a: Nat, +b: Nat,
                 h: {Nat.is_lt(a, b) == True{} : Bool},
                 hb: R.le_ok(b, n))
    -> {Nat.is_ne(Nat.sub(n, a), Nat.sub(n, b)) == True{} : Bool}:
  ne_symm(Nat.sub(n, b), Nat.sub(n, a),
          lt_imp_ne(Nat.sub(n, b), Nat.sub(n, a),
                    sub_lt_mono(n, a, b, h, hb)))

def Laws.delay_injective(n, a, b, h, hb):
  delay_inj_go(n, a, b, h, hb)

# --------------------------------------------------------------------------
# 6. the ok(cfg)=True law family
# --------------------------------------------------------------------------

# and-elimination, both halves
def and_elim_l_go(a: Bool, b: Bool, +h: {Bool.and(a, b) == True{} : Bool})
    -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Bool.fne({False{} == True{} : Bool}, h)

def Laws.and_elim_l(a, b, h):
  and_elim_l_go(a, b, h)

def and_elim_r_go(a: Bool, b: Bool, +h: {Bool.and(a, b) == True{} : Bool})
    -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Bool.fne({b == True{} : Bool}, h)

def Laws.and_elim_r(a, b, h):
  and_elim_r_go(a, b, h)

# ok decomposes: the outer and's left half is lanes_ok
def Laws.ok_lanes(c, h):
  and_elim_l_go(R.lanes_ok(R.cfg_lanes(c)),
                Bool.and(R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c), R.cfg_projs(c)),
                         R.writes_unique(R.cfg_projs(c))),
                h)

# the outer and's right half, decomposed again
def Laws.ok_projs(c, h):
  and_elim_l_go(R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c), R.cfg_projs(c)),
                R.writes_unique(R.cfg_projs(c)),
                and_elim_r_go(R.lanes_ok(R.cfg_lanes(c)),
                              Bool.and(R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c), R.cfg_projs(c)),
                                       R.writes_unique(R.cfg_projs(c))),
                              h))

def Laws.ok_unique(c, h):
  and_elim_r_go(R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c), R.cfg_projs(c)),
                R.writes_unique(R.cfg_projs(c)),
                and_elim_r_go(R.lanes_ok(R.cfg_lanes(c)),
                              Bool.and(R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c), R.cfg_projs(c)),
                                       R.writes_unique(R.cfg_projs(c))),
                              h))

# per-edge decomposition of projs_shape_ok
def projs_ok_cons_go(+nlanes: Nat, +horizon: Nat, +p: R.Proj,
                     +ps: List<&2, R.Proj>,
                     +h: {R.projs_shape_ok(nlanes, horizon, p <> ps) == True{} : Bool})
    -> {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool}:
  and_elim_l_go(R.proj_shape_ok(nlanes, horizon, p),
                R.projs_shape_ok(nlanes, horizon, ps), h)

def Laws.projs_ok_cons(nlanes, horizon, p, ps, h):
  projs_ok_cons_go(nlanes, horizon, p, ps, h)

def projs_ok_tail_go(+nlanes: Nat, +horizon: Nat, +p: R.Proj,
                     +ps: List<&2, R.Proj>,
                     +h: {R.projs_shape_ok(nlanes, horizon, p <> ps) == True{} : Bool})
    -> {R.projs_shape_ok(nlanes, horizon, ps) == True{} : Bool}:
  and_elim_r_go(R.proj_shape_ok(nlanes, horizon, p),
                R.projs_shape_ok(nlanes, horizon, ps), h)

def Laws.projs_ok_tail(nlanes, horizon, p, ps, h):
  projs_ok_tail_go(nlanes, horizon, p, ps, h)

# proj_shape_ok's delay conjunct
def proj_delay_fits_go(+nlanes: Nat, +horizon: Nat, +p: R.Proj,
                       h: {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool})
    -> {Nat.is_le(Nat.add(R.proj_d(p), 1n), horizon) == True{} : Bool}:
  h_rest = and_elim_r_go(Nat.is_lt(R.proj_src(p), nlanes),
                         Bool.and(Nat.is_lt(R.proj_tgt(p), nlanes),
                                  Bool.and(Nat.is_le(Nat.add(R.proj_d(p), 1n), horizon),
                                           Nat.is_le(Nat.add(R.proj_d(p), R.proj_win(p)), horizon))),
                         h)
  h_rest2 = and_elim_r_go(Nat.is_lt(R.proj_tgt(p), nlanes),
                          Bool.and(Nat.is_le(Nat.add(R.proj_d(p), 1n), horizon),
                                   Nat.is_le(Nat.add(R.proj_d(p), R.proj_win(p)), horizon)),
                          h_rest)
  and_elim_l_go(Nat.is_le(Nat.add(R.proj_d(p), 1n), horizon),
                Nat.is_le(Nat.add(R.proj_d(p), R.proj_win(p)), horizon),
                h_rest2)

def Laws.proj_delay_fits(nlanes, horizon, p, h):
  proj_delay_fits_go(nlanes, horizon, p, h)

# proj_shape_ok's window conjunct: peel the three leading and-conjuncts
def proj_win_fits_go(+nlanes: Nat, +horizon: Nat, +p: R.Proj,
                     h: {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool})
    -> {Nat.is_le(Nat.add(R.proj_d(p), R.proj_win(p)), horizon) == True{} : Bool}:
  h_rest = and_elim_r_go(Nat.is_lt(R.proj_src(p), nlanes),
                         Bool.and(Nat.is_lt(R.proj_tgt(p), nlanes),
                                  Bool.and(Nat.is_le(Nat.add(R.proj_d(p), 1n), horizon),
                                           Nat.is_le(Nat.add(R.proj_d(p), R.proj_win(p)), horizon))),
                         h)
  h_rest2 = and_elim_r_go(Nat.is_lt(R.proj_tgt(p), nlanes),
                          Bool.and(Nat.is_le(Nat.add(R.proj_d(p), 1n), horizon),
                                   Nat.is_le(Nat.add(R.proj_d(p), R.proj_win(p)), horizon)),
                          h_rest)
  and_elim_r_go(Nat.is_le(Nat.add(R.proj_d(p), 1n), horizon),
                Nat.is_le(Nat.add(R.proj_d(p), R.proj_win(p)), horizon),
                h_rest2)

def Laws.proj_win_fits(nlanes, horizon, p, h):
  proj_win_fits_go(nlanes, horizon, p, h)

# lanes_ok decomposes per-cons
def lanes_ok_cons_go(+k: Nat, +ks: List<&2, Nat>,
                     h: {R.lanes_ok(k <> ks) == True{} : Bool})
    -> {Nat.is_ge(k, 1n) == True{} : Bool}:
  and_elim_l_go(Nat.is_ge(k, 1n), R.lanes_ok(ks), h)

def Laws.lanes_ok_cons(k, ks, h):
  lanes_ok_cons_go(k, ks, h)

def lanes_ok_tail_go(+k: Nat, +ks: List<&2, Nat>,
                     h: {R.lanes_ok(k <> ks) == True{} : Bool})
    -> {R.lanes_ok(ks) == True{} : Bool}:
  and_elim_r_go(Nat.is_ge(k, 1n), R.lanes_ok(ks), h)

def Laws.lanes_ok_tail(k, ks, h):
  lanes_ok_tail_go(k, ks, h)

# the src conjunct is the FIRST and of proj_shape_ok
def proj_src_bounded_go(+nlanes: Nat, +horizon: Nat, +p: R.Proj,
                        h: {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool})
    -> {Nat.is_lt(R.proj_src(p), nlanes) == True{} : Bool}:
  and_elim_l_go(Nat.is_lt(R.proj_src(p), nlanes),
                Bool.and(Nat.is_lt(R.proj_tgt(p), nlanes),
                         Bool.and(Nat.is_le(Nat.add(R.proj_d(p), 1n), horizon),
                                  Nat.is_le(Nat.add(R.proj_d(p), R.proj_win(p)), horizon))),
                h)

def Laws.proj_src_bounded(nlanes, horizon, p, h):
  proj_src_bounded_go(nlanes, horizon, p, h)

# the tgt conjunct: peel src first, then take the left half
def proj_tgt_bounded_go(+nlanes: Nat, +horizon: Nat, +p: R.Proj,
                        h: {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool})
    -> {Nat.is_lt(R.proj_tgt(p), nlanes) == True{} : Bool}:
  h_rest = and_elim_r_go(Nat.is_lt(R.proj_src(p), nlanes),
                         Bool.and(Nat.is_lt(R.proj_tgt(p), nlanes),
                                  Bool.and(Nat.is_le(Nat.add(R.proj_d(p), 1n), horizon),
                                           Nat.is_le(Nat.add(R.proj_d(p), R.proj_win(p)), horizon))),
                         h)
  and_elim_l_go(Nat.is_lt(R.proj_tgt(p), nlanes),
                Bool.and(Nat.is_le(Nat.add(R.proj_d(p), 1n), horizon),
                         Nat.is_le(Nat.add(R.proj_d(p), R.proj_win(p)), horizon)),
                h_rest)

def Laws.proj_tgt_bounded(nlanes, horizon, p, h):
  proj_tgt_bounded_go(nlanes, horizon, p, h)

# lookup bricks: both are definitional once the cons pattern opens
def Laws.nth_init_zero(k, ks):
  match ks:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def Laws.nth_init_succ(k, ks, i):
  {==}

# --------------------------------------------------------------------------
# 0e. add/mul rearrangement bricks (for the Q1 staleness capstones)
# --------------------------------------------------------------------------
# a + b == b + a by induction on a, peeling one succ at a time to the
# front of the RIGHT operand via the flipped add_succ.
def add_comm_go(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Laws.add_zero(b))
    case 1n++p:
      %Equal.sym(Nat, Nat.add(p, b), Nat.add(b, p), add_comm_go(p, b))
        : {1n+_ == Nat.add(b, 1n+p) : Nat}
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Laws.add_succ(b, p))
        : {1n+Nat.add(b, p) == _ : Nat}
      {==}

# (a + b) + c == a + (b + c) by induction on a (both sides peel in sync)
def add_assoc_go(a: Nat, +b: Nat, +c: Nat)
    -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c),
                 Nat.add(p, Nat.add(b, c)), add_assoc_go(p, b, c))

def Laws.add_comm(a, b):
  add_comm_go(a, b)

def Laws.add_assoc(a, b, c):
  add_assoc_go(a, b, c)

# (a + b) - a == b by induction on a: both sides lose one succ per peel.
# The affinely-correct shape: a is the induction variable (used twice
# above, but each use is a distinct -binder pattern split, so the peel is
# on the live first argument and the step case recurses with one less).
def sub_add_r_go(a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      Laws.sub_zero_r(b)
    case 1n++p:
      sub_add_r_go(p, b)

def Laws.sub_add_r(a, b):
  sub_add_r_go(a, b)

# --------------------------------------------------------------------------
# 1d. the Q1 staleness capstones
# --------------------------------------------------------------------------
# canonical_run: q whole periods advance newest by exactly q and return the
# countdown to its canonical rest position k-1.  Induction on q with the
# starting count GENERALIZED (the succ case recurses at n+1, one period
# in).  Nat.mul(1+p, k) reduces to k + p*k, so run_segmentable(k, p*k)
# peels the NEW period first; period_from_init closes it, and the add_assoc
# brick regroups n+1+p into (n+1)+p for the induction hypothesis.
# add(n, 1+p) == add(1+n, p): the successor can be peeled off either
# operand; the canonical_run induction needs it to hand the lane's count
# (reduced to 1+n by period_from_init) to the hypothesis-shape add(1+n, p).
def add_swap_one(+n: Nat, +p: Nat)
    -> {Nat.add(n, 1n+p) == Nat.add(1n+n, p) : Nat}:
  Laws.add_succ(n, p)

# the period step for k a KNOWN successor, stated at the countdown's
# reduced normal form (sub(1+kk, 1n) normalizes to sub(kk, 0n), NOT to
# kk -- sub is stuck on an abstract first argument).  countdown_publish
# consumes the countdown directly; the two lane-side normal forms are
# bridged by sub_zero_r and the tick's two succ-shapes by add_one.
def period_from_init_pos(+kk: Nat, +n: Nat)
    -> {R.steps(1n+kk, R.Lane{1n+kk, kk, n})
          == R.Lane{1n+kk, kk, 1n+n} : R.Lane}:
  Equal.trans(R.Lane,
    R.steps(1n+kk, R.Lane{1n+kk, kk, n}),
    R.steps(Nat.add(kk, 1n), R.Lane{1n+kk, kk, n}),
    R.Lane{1n+kk, kk, 1n+n},
    Equal.cong(Nat, R.Lane, z => R.steps(z, R.Lane{1n+kk, kk, n}),
               1n+kk, Nat.add(kk, 1n),
               Equal.sym(Nat, Nat.add(kk, 1n), 1n+kk, Laws.add_one(kk))),
    Equal.trans(R.Lane,
      R.steps(Nat.add(kk, 1n), R.Lane{1n+kk, kk, n}),
      R.Lane{1n+kk, Nat.sub(kk, 0n), 1n+n},
      R.Lane{1n+kk, kk, 1n+n},
      Laws.countdown_publish(kk, 1n+kk, n),
      Equal.cong(Nat, R.Lane, z => R.Lane{1n+kk, z, 1n+n},
                 Nat.sub(kk, 0n), kk, Laws.sub_zero_r(kk))))

# the k >= 1 body, stated structurally at k = 1+kk with the countdown at
# its reduced normal form kk, so no is_ge witness is passed down the
# recursion (each level rebuilds it for free from the successor
# structure).  Induction on q, count generalized.
def canonical_run_pos(q: Nat, +kk: Nat, +n: Nat)
    -> {R.steps(Nat.mul(q, 1n+kk), R.Lane{1n+kk, kk, n})
          == R.Lane{1n+kk, kk, Nat.add(n, q)} : R.Lane}:
  match q:
    case 0n:
      Equal.cong(Nat, R.Lane, z => R.Lane{1n+kk, kk, z}, n, Nat.add(n, 0n),
                 Equal.sym(Nat, Nat.add(n, 0n), n, Laws.add_zero(n)))
    case 1n++p:
      Equal.trans(R.Lane,
        R.steps(Nat.add(1n+kk, Nat.mul(p, 1n+kk)), R.Lane{1n+kk, kk, n}),
        R.steps(Nat.mul(p, 1n+kk), R.steps(1n+kk, R.Lane{1n+kk, kk, n})),
        R.Lane{1n+kk, kk, Nat.add(n, 1n+p)},
        Laws.run_segmentable(1n+kk, Nat.mul(p, 1n+kk), R.Lane{1n+kk, kk, n}),
        Equal.trans(R.Lane,
          R.steps(Nat.mul(p, 1n+kk), R.steps(1n+kk, R.Lane{1n+kk, kk, n})),
          R.steps(Nat.mul(p, 1n+kk), R.Lane{1n+kk, kk, 1n+n}),
          R.Lane{1n+kk, kk, Nat.add(n, 1n+p)},
          Equal.cong(R.Lane, R.Lane, z => R.steps(Nat.mul(p, 1n+kk), z),
                     R.steps(1n+kk, R.Lane{1n+kk, kk, n}),
                     R.Lane{1n+kk, kk, 1n+n},
                     period_from_init_pos(kk, n)),
          Equal.trans(R.Lane,
            R.steps(Nat.mul(p, 1n+kk), R.Lane{1n+kk, kk, 1n+n}),
            R.Lane{1n+kk, kk, Nat.add(1n+n, p)},
            R.Lane{1n+kk, kk, Nat.add(n, 1n+p)},
            canonical_run_pos(p, kk, 1n+n),
            Equal.cong(Nat, R.Lane, z => R.Lane{1n+kk, kk, z},
                       Nat.add(1n+n, p), Nat.add(n, 1n+p),
                       Equal.sym(Nat, Nat.add(n, 1n+p), Nat.add(1n+n, p),
                                 add_swap_one(n, p))))))

# the dispatcher: k = 0 refuted by the ge witness (is_ge(0n, 1n) is
# False); k = 1+kk delegates to the structural body, bridging the law's
# countdown shape (sub(1+kk, 1n), normalizing to sub(kk, 0n)) to the
# body's kk on both sides of the equation.
def canonical_run_go(q: Nat, +k: Nat, +n: Nat,
                     h: {Nat.is_ge(k, 1n) == True{} : Bool})
    -> {R.steps(Nat.mul(q, k), R.Lane{k, Nat.sub(k, 1n), n})
          == R.Lane{k, Nat.sub(k, 1n), Nat.add(n, q)} : R.Lane}:
  match k:
    case 0n:
      Bool.fne({R.steps(Nat.mul(q, 0n), R.Lane{0n, Nat.sub(0n, 1n), n})
                  == R.Lane{0n, Nat.sub(0n, 1n), Nat.add(n, q)} : R.Lane}, h)
    case 1n+kk:
      Equal.trans(R.Lane,
        R.steps(Nat.mul(q, 1n+kk), R.Lane{1n+kk, Nat.sub(kk, 0n), n}),
        R.steps(Nat.mul(q, 1n+kk), R.Lane{1n+kk, kk, n}),
        R.Lane{1n+kk, Nat.sub(kk, 0n), Nat.add(n, q)},
        Equal.cong(R.Lane, R.Lane, l => R.steps(Nat.mul(q, 1n+kk), l),
                   R.Lane{1n+kk, Nat.sub(kk, 0n), n}, R.Lane{1n+kk, kk, n},
                   Equal.cong(Nat, R.Lane, z => R.Lane{1n+kk, z, n},
                              Nat.sub(kk, 0n), kk, Laws.sub_zero_r(kk))),
        Equal.trans(R.Lane,
          R.steps(Nat.mul(q, 1n+kk), R.Lane{1n+kk, kk, n}),
          R.Lane{1n+kk, kk, Nat.add(n, q)},
          R.Lane{1n+kk, Nat.sub(kk, 0n), Nat.add(n, q)},
          canonical_run_pos(q, kk, n),
          Equal.cong(Nat, R.Lane, z => R.Lane{1n+kk, z, Nat.add(n, q)},
                     kk, Nat.sub(kk, 0n),
                     Equal.sym(Nat, Nat.sub(kk, 0n), kk, Laws.sub_zero_r(kk)))))

def Laws.canonical_run(k, q, n, h):
  canonical_run_go(q, k, n, h)

# --------------------------------------------------------------------------
# 1d (cont.). newest_at and stale_bound: the Q1 capstones
# --------------------------------------------------------------------------
# newest_at: at t = q*k + r with r <= k-1, the newest sample is exactly
# n + q.  Split the run at q*k (run_segmentable), advance the whole
# periods with canonical_run (that half is EXACTLY its conclusion), then
# hold through the remainder r with hold_until_due -- whose hypothesis
# r < (k-1) + 1 comes from r <= k-1 by le_lt_succ, and whose countdown
# argument k-1 is what canonical_run leaves behind.
# is_le(r, m) gives is_lt(r, m + 1) -- in the ADD normal form
# (add(m, 1n), the shape hold_until_due's hypothesis normalizes to).
def lt_succ_add(r: Nat, +m: Nat, h: {Nat.is_le(r, m) == True{} : Bool})
    -> {Nat.is_lt(r, Nat.add(m, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(m, 1n), 1n+m, Laws.add_one(m))
    : {Nat.is_lt(r, _) == True{} : Bool}
  le_lt_succ(r, m, h)

def newest_at_go(+k: Nat, +q: Nat, +r: Nat, +n: Nat,
                 h: {Nat.is_ge(k, 1n) == True{} : Bool},
                 hr: {Nat.is_le(r, Nat.sub(k, 1n)) == True{} : Bool})
    -> {R.lane_newest(R.steps(Nat.add(Nat.mul(q, k), r), R.Lane{k, Nat.sub(k, 1n), n}))
          == Nat.add(n, q) : Nat}:
  %Equal.sym(R.Lane, R.steps(Nat.add(Nat.mul(q, k), r), R.Lane{k, Nat.sub(k, 1n), n}),
             R.steps(r, R.steps(Nat.mul(q, k), R.Lane{k, Nat.sub(k, 1n), n})),
             Laws.run_segmentable(Nat.mul(q, k), r, R.Lane{k, Nat.sub(k, 1n), n}))
    : {R.lane_newest(_) == Nat.add(n, q) : Nat}
  %Equal.sym(R.Lane, R.steps(Nat.mul(q, k), R.Lane{k, Nat.sub(k, 1n), n}),
             R.Lane{k, Nat.sub(k, 1n), Nat.add(n, q)},
             Laws.canonical_run(k, q, n, h))
    : {R.lane_newest(R.steps(r, _)) == Nat.add(n, q) : Nat}
  Laws.hold_until_due(r, k, Nat.sub(k, 1n), Nat.add(n, q),
                      lt_succ_add(r, Nat.sub(k, 1n), hr))

def Laws.newest_at(k, q, r, n, h, hr):
  newest_at_go(k, q, r, n, h, hr)

# stale_bound: the age of the newest sample at t = q*k + r is the
# remainder r, which the witness bounds by k-1.  Pure arithmetic: the
# hypothesis rewrites t into q*k + r, then cancelling the q*k (sub_add_r)
# leaves exactly r, and hr is the bound.
def Laws.stale_bound(k, q, r, t, h, hr, ht):
  %Equal.sym(Nat, t, Nat.add(Nat.mul(q, k), r), ht) : {Nat.is_le(Nat.sub(_, Nat.mul(q, k)), Nat.sub(k, 1n)) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(Nat.add(Nat.mul(q, k), r), Nat.mul(q, k)), r,
             Laws.sub_add_r(Nat.mul(q, k), r))
    : {Nat.is_le(_, Nat.sub(k, 1n)) == True{} : Bool}
  hr

# --------------------------------------------------------------------------
# 3b. the window order laws
# --------------------------------------------------------------------------
# sub is antitone (non-strict) in its second argument inside the history:
# a <= b <= n implies n-b <= n-a.  Same induction skeleton as the strict
# sub_lt_mono: peel (n, b) in lockstep; a=0 closes by sub_le_self +
# sub_le_b; the saturated b > n case is refuted by the le_ok witness.
# sub is antitone (non-strict) in its second argument inside the
# history: a <= b <= n implies n-b <= n-a.  Same induction skeleton as
# the strict sub_lt_mono: peel (n, a, b) together; the saturated
# b > n case is refuted by the le_ok witness; b=0 closes the sub side
# (nothing cancelled) and a=0 cancels maximally (sub_le_self).
def sub_le_mono_go2(+n: Nat, +a: Nat, +b: Nat,
                    h: {Nat.is_le(a, b) == True{} : Bool},
                    hb: R.le_ok(b, n))
    -> {Nat.is_le(Nat.sub(n, b), Nat.sub(n, a)) == True{} : Bool}:
  match n a b:
    case 0n 0n _:
      {==}
    case 0n 1n+r _:
      {==}
    case 1n+p 0n 0n:
      Laws.le_refl_b(Nat.sub(1n+p, 0n))
    case 1n+p 0n 1n+q:
      Laws.le_succ_of_le(Nat.sub(p, q), p, Laws.sub_le_b(p, q))
    case 1n+p 1n+r 0n:
      Bool.fne({Nat.is_le(Nat.sub(1n+p, 0n), Nat.sub(1n+p, 1n+r)) == True{} : Bool},
               Bool.fne({Nat.is_le(1n+r, 0n) == True{} : Bool}, h))
    case 1n+p 1n+r 1n+q:
      sub_le_mono_go2(p, r, q, h, hb)

def Laws.sub_le_mono(n, a, b, h, hb):
  sub_le_mono_go2(n, a, b, h, hb)

# window_ordered: the window's ends are in order, lo <= hi, whenever the
# window fits the history (d + w <= n).  Pure sub_le_mono at a=d, b=d+w
# (d <= d+w by le_add_one-style step): lo = n-(d+w) <= n-d = hi.
def le_add_r(+d: Nat, w: Nat) -> {Nat.is_le(d, Nat.add(d, w)) == True{} : Bool}:
  match w:
    case 0n:
      %Equal.sym(Nat, Nat.add(d, 0n), d, Laws.add_zero(d))
        : {Nat.is_le(d, _) == True{} : Bool}
      Laws.le_refl_b(d)
    case 1n++q:
      %Equal.sym(Nat, Nat.add(d, 1n+q), Nat.add(1n+d, q), add_swap_one(d, q))
        : {Nat.is_le(d, _) == True{} : Bool}
      Laws.le_succ_of_le(d, Nat.add(d, q), le_add_r(d, q))

def window_ordered_go(n: Nat, +d: Nat, +w: Nat,
                       h: R.le_ok(Nat.add(d, w), n))
    -> {Nat.is_le(R.win_lo(R.route_window(n, d, w)),
                             R.win_hi(R.route_window(n, d, w))) == True{} : Bool}:
  sub_le_mono_go2(n, d, Nat.add(d, w), le_add_r(d, w), h)

def Laws.window_ordered(n, d, w, h):
  window_ordered_go(n, d, w, h)

# --------------------------------------------------------------------------
# 3c. the list-level routing laws: many lanes, many projections
# --------------------------------------------------------------------------

# lanes_step_local: induction on ls.  The bounds witness kills the Nil
# case before it can lie (lt_ok(i, 0) is Empty): the default branch of
# nth_lane is never reached under the hypothesis.  In the cons case,
# i = 0 is reflexivity (both sides see the head), and the tail's own
# bound lt_ok(p, lanes_len(t)) follows from lt_ok(1+p, 1+len) by
# unfolding le_ok once -- definitional, no rewrite needed.
# the Nil bounds are absurd: lt_ok(i, 0) is le_ok(1+i, 0), which is
# Empty for every i (match on i unfolds le_ok to Empty either way).
def lt_ok_nil_absurd(i: Nat, h: R.le_ok(Nat.add(i, 1n), 0n)) -> Empty:
  match i h:
    case 0n h:
      h
    case 1n+p h:
      h

def lanes_step_local_go(+ls: List<&2, R.Lane>, i: Nat,
                        h: R.lt_ok(i, R.lanes_len(ls)))
  -> {R.nth_lane(R.lanes_step(ls), i)
        == R.step_lane(R.nth_lane(ls, i))  : R.Lane}:
  match ls i h:
    case Nil{} _ h:
      Empty.absurd({R.nth_lane(R.lanes_step(Nil{}) , i)
                      == R.step_lane(R.nth_lane(Nil{}, i)) : R.Lane},
                     lt_ok_nil_absurd(i, h))
    case h <> t 0n _:
      {==}
    case h <> t 1n+p hlt:
      lanes_step_local_go(t, p, hlt)

def Laws.lanes_step_local(ls, i, h):
  lanes_step_local_go(ls, i, h)

# route_pointwise: same shape, on the projection list.  The lanes list
# is only read (route_proj never consumes it destructively), so the
# induction is purely on ps; ls rides along as a + parameter.
def route_pointwise_go(+ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>, i: Nat,
                       h: R.lt_ok(i, R.projs_len(ps)))
  -> {R.nth_line(R.route_all(ls, ps), i)
        == R.route_proj(ls, R.nth_proj(ps, i))  : R.Line}:
  match ps i h:
    case Nil{} _ h:
      Empty.absurd({R.nth_line(R.route_all(ls, Nil{}) , i)
                      == R.route_proj(ls, R.nth_proj(Nil{}, i)) : R.Line},
                     lt_ok_nil_absurd(i, h))
    case h <> t 0n _:
      {==}
    case h <> t 1n+p hlt:
      route_pointwise_go(ls, t, p, hlt)

def Laws.route_pointwise(ls, ps, i, h):
  route_pointwise_go(ls, ps, i, h)

# tick_split: chunk safety at the full Tick.  Induction on a, exactly
# as run_segmentable but lifted to the pair: 0 + b = b is reflexivity;
# 1 + (p + b) peels one tick (ticks steps the FRONT) and the recursive
# call continues from the stepped lanes -- the go-form puts the
# shrinking a FIRST so the termination check sees it decrease.
def tick_split_go(a: Nat, +ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>,
                  b: Nat)
  -> {R.ticks(Nat.add(a, b), ls, ps)
        == R.ticks(b, R.tick_lanes(R.ticks(a, ls, ps)), ps) : R.Tick}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      tick_split_go(p, R.tick_lanes(R.tick(ls, ps)), ps, b)

def Laws.tick_split(ls, ps, a, b):
  tick_split_go(a, ls, ps, b)

# macro_degenerate: at k=1 the macro-first read (d=1, fraction 0/1) is
# the staggered point read.  steps(t, Lane{1,0,0}) keeps newest = t
# (lane_newest_k1 at n=0), so the goal reduces to
#   i0(route_read(t, 1, 0, 1, win)) == t - 0 = t
# and route_read at d=1n+0n answers Line{t-1, t, ...}: both sides are
# structural reflexivity after one unfolding of route_read's d=1+dp
# branch at dp=0 and Laws.sub_zero.
def macro_degenerate_go(+t: Nat, +win: Nat)
  -> {R.l_i0(R.route_read(R.lane_newest(R.steps(t, R.Lane{1n, 0n, 0n})),
                          1n, R.lane_num(R.steps(t, R.Lane{1n, 0n, 0n})),
                          1n, win))
        == Nat.sub(t, 1n) : Nat}:
  %Equal.sym(Nat, R.lane_newest(R.steps(t, R.Lane{1n, 0n, 0n})), t,
             newest_k1_t(t))
    : {Nat.sub(_, 1n) == Nat.sub(t, 1n) : Nat}
  {==}

def Laws.macro_degenerate(t, win):
  macro_degenerate_go(t, win)

# --------------------------------------------------------------------------
# 3e. the slow-side lag necessity laws
# --------------------------------------------------------------------------

# slow_lag_bound: the windowed read's freshest member t-d is behind the
# head t -- sub_le_b is exactly this (sub never exceeds its first arg).
def Laws.slow_lag_bound(t, d):
  Laws.sub_le_b(t, d)

# window_head_age: the window's head lo = n - (d+k) is EXACTLY d+k
# # behind the head of the stream: adding the span back cancels to n.
# route_window(n, d, k) = Win{n - (d+k), n - d}, so the goal is
#   (n - (d+k)) + (d+k) == n  under le_ok(d+k, n),
# which is sub_add_cancel with the add_comm/assoc rearrangement.
def window_head_age_go(+n: Nat, +d: Nat, +k: Nat,
                       h: R.le_ok(Nat.add(d, k), n))
  -> {Nat.add(R.win_lo(R.route_window(n, d, k)), Nat.add(d, k)) == n : Nat}:
  %Laws.sub_add_cancel(n, Nat.add(d, k),
                       Laws.le_ok_iff(Nat.add(d, k), n, h))
    : {Nat.add(R.win_lo(R.route_window(n, d, k)), Nat.add(d, k)) == _ : Nat}
  {==}

def Laws.window_head_age(n, d, k, h):
  window_head_age_go(n, d, k, h)

# --------------------------------------------------------------------------
# 4. the end-to-end freshness laws
# --------------------------------------------------------------------------

# route_all_len: induction on ps; both sides reduce to 1+len(tail).
def route_all_len_go(+ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>)
  -> {R.lines_len(R.route_all(ls, ps)) == R.projs_len(ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case h <> t:
      %route_all_len_go(ls, t)
        : {Nat.add(1n, R.lines_len(R.route_all(ls, t))) == Nat.add(1n, _) : Nat}
      {==}

def Laws.route_all_len(ls, ps):
  route_all_len_go(ls, ps)

# line_ordered: case on d.  d=0 clamps i0=i1=n (le_refl_b); d>=1 asks
# sub(n, 1+dp) <= sub(n, dp), proved by double induction: both sides of
# Nat.sub reduce on BOTH arguments, so the goal in the (1+np, 1+dq) case
# IS the same claim at (np, dq) -- the recursion is on n.
def line_ordered_go(n: Nat, +dp: Nat)
  -> {Nat.is_le(Nat.sub(n, Nat.add(1n, dp)), Nat.sub(n, dp))
        == True{} : Bool}:
  match n dp:
    case 0n _:
      {==}
    case 1n++np 0n:
      %Equal.sym(Nat, Nat.sub(np, 0n), np, Laws.sub_zero(np))
        : {Nat.is_le(_, 1n+np) == True{} : Bool}
      Laws.le_succ_b(np)
    case 1n+np 1n+dq:
      line_ordered_go(np, dq)

def Laws.line_ordered(n, d, num, den, win):
  match d:
    case 0n:
      Laws.le_refl_b(n)
    case 1n+dp:
      line_ordered_go(n, dp)

# route_fresh: the pointwise brick.  route_proj(ls, p) is route_read at
# n = lane_newest(nth_lane(ls, proj_src(p))), d = proj_d(p) -- and
# read_fresh at exactly those arguments closes the goal.
def Laws.route_fresh(ls, p):
  Laws.read_fresh(R.lane_newest(R.nth_lane(ls, R.proj_src(p))),
                  R.proj_d(p),
                  R.lane_num(R.nth_lane(ls, R.proj_src(p))),
                  R.lane_k(R.nth_lane(ls, R.proj_src(p))),
                  R.proj_win(p))

# read_fresh_tick: tick steps then routes, so the goal reduces to the
# per-projection freshness against the stepped lanes -- proved by the
# same induction-on-ps shape as route_pointwise (lanes_step_local's
# sibling), with route_fresh closing each head and the bounds witness
# killing the Nil case.
def read_fresh_tick_go(+ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>,
                       i: Nat, h: R.lt_ok(i, R.projs_len(ps)))
  -> {Nat.is_le(R.l_i1(R.nth_line(R.tick_lines(R.tick(ls, ps)), i)),
                R.lane_newest(R.nth_lane(R.lanes_step(ls),
                                          R.proj_src(R.nth_proj(ps, i)))))
        == True{} : Bool}:
  match ps i h:
    case Nil{} _ h:
      Empty.absurd({Nat.is_le(R.l_i1(R.nth_line(R.route_all(R.lanes_step(ls), Nil{}), i)),
                               R.lane_newest(R.nth_lane(R.lanes_step(ls),
                                                        R.proj_src(R.nth_proj(Nil{}, i)))))
                     == True{} : Bool},
                   lt_ok_nil_absurd(i, h))
    case p <> t 0n _:
      Laws.route_fresh(R.lanes_step(ls), p)
    case p <> t 1n+q hlt:
      read_fresh_tick_go(ls, t, q, hlt)

def Laws.read_fresh_tick(ls, ps, i, h):
  read_fresh_tick_go(ls, ps, i, h)

# the t=0 base: the initial Tick routes against ls itself -- the same
# induction-on-ps shape, route_fresh closing each head.
def read_fresh_nil_go(+ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>,
                      i: Nat, h: R.lt_ok(i, R.projs_len(ps)))
  -> {Nat.is_le(R.l_i1(R.nth_line(R.tick_lines(R.ticks(0n, ls, ps)), i)),
                R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(0n, ls, ps)),
                                          R.proj_src(R.nth_proj(ps, i)))))
        == True{} : Bool}:
  match ps i h:
    case Nil{} _ h:
      Empty.absurd({Nat.is_le(R.l_i1(R.nth_line(R.route_all(ls, Nil{}), i)),
                               R.lane_newest(R.nth_lane(ls,
                                                        R.proj_src(R.nth_proj(Nil{}, i)))))
                     == True{} : Bool},
                   lt_ok_nil_absurd(i, h))
    case p <> t 0n _:
      Laws.route_fresh(ls, p)
    case p <> t 1n+q hlt:
      read_fresh_nil_go(ls, t, q, hlt)

# read_fresh_ticks: induction on t.  t=0 is the initial Tick (routes
# against ls itself -- route_fresh at the unstepped lanes); the step
# case peels one tick and continues from the stepped lanes, which is
# exactly tick_split's composition: freshness at t+1 is freshness at 1
# from the state freshness held at t.
def read_fresh_ticks_go(t: Nat, +ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>,
                        i: Nat, h: R.lt_ok(i, R.projs_len(ps)))
  -> {Nat.is_le(R.l_i1(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                          R.proj_src(R.nth_proj(ps, i)))))
        == True{} : Bool}:
  match t:
    case 0n:
      read_fresh_nil_go(ls, ps, i, h)
    case 1n+q:
      read_fresh_ticks_go(q, R.tick_lanes(R.tick(ls, ps)), ps, i, h)

def Laws.read_fresh_ticks(ls, ps, t, i, h):
  read_fresh_ticks_go(t, ls, ps, i, h)

# --------------------------------------------------------------------------
# 4b. the non-aliasing laws
# --------------------------------------------------------------------------

# eq_of_is_eq: the decider True means definitionally equal Nats.  The
# double-succ case recurses (cmp peels both); the mismatched cases are
# absurd (a False decider cannot be True).
def eq_of_is_eq_go(a: Nat, b: Nat,
                   +h: {Nat.is_eq(a, b) == True{} : Bool})
    -> {a == b : Nat}:
  match a b h:
    case 0n 0n _:
      {==}
    case 0n 1n+q h:
      Bool.fne({0n == 1n+q : Nat}, h)
    case 1n+p 0n h:
      Bool.fne({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q h:
      %eq_of_is_eq_go(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}
def Laws.eq_of_is_eq(a, b, h):
  eq_of_is_eq_go(a, b, h)

# lt_of_le_succ: d+1 <= b is d < b.  0 < b always; 1+p <= 0 absurd;
# the double-succ case is the recursive claim (is_le(1+p,1+q) IS the
# decider on (p,q), and so is is_lt).
def lt_of_le_succ_go(a: Nat, b: Nat,
                     +h: {Nat.is_le(Nat.add(a, 1n), b) == True{} : Bool})
    -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b h:
    case 0n 0n h:
      Bool.fne({Nat.is_le(Nat.add(0n, 1n), 0n) == True{} : Bool}, h)
    case 0n 1n+q _:
      {==}
    case 1n+p 0n h:
      Bool.fne({Nat.is_le(Nat.add(1n+p, 1n), 0n) == True{} : Bool}, h)
    case 1n+p 1n+q h:
      lt_of_le_succ_go(p, q, h)
def Laws.lt_of_le_succ(a, b, h):
  lt_of_le_succ_go(a, b, h)

# fits_lt: peel proj_shape_ok's conjuncts to the delay one, then shift
# the +1: d + 1 <= horizon is d < horizon.
def Laws.fits_lt(nlanes, horizon, p, h):
  lt_of_le_succ_go(R.proj_d(p), horizon,
                   proj_delay_fits_go(nlanes, horizon, p, h))

# clamp_distinct: the head n is never the delayed index n-(1+dp) once
# 1+dp <= n.  n=0 is Empty (le_ok(1+dp, 0) uninhabited); at n=1+p the
# subtraction peels to sub(p, dp), which is < 1+p by sub_le_self +
# le_lt_succ -- strict, so lt_imp_ne + ne_symm give the disequality.
def clamp_distinct_go(n: Nat, +dp: Nat,
                      hb: R.le_ok(Nat.add(1n, dp), n))
    -> {Nat.is_ne(n, Nat.sub(n, Nat.add(1n, dp))) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_ne(0n, Nat.sub(0n, Nat.add(1n, dp))) == True{} : Bool}, hb)
    case 1n++p:
      ne_symm(Nat.sub(p, dp), 1n+p,
              lt_imp_ne(Nat.sub(p, dp), 1n+p,
                        le_lt_succ(Nat.sub(p, dp), p,
                                   Laws.sub_le_self(p, dp))))
def Laws.clamp_distinct(n, dp, hb):
  clamp_distinct_go(n, dp, hb)

# read_distinct: split on the clamp.  da=0 is clamp_distinct (db=1+dq,
# the delayed read is in the horizon); da=1+dap is delay_inj_go at the
# reduced normal form of both reads (route_read's d>=1 branch peels the
# 1 off the delay, and l_i0 of it is n-(1+dap)).
def read_distinct_go(n: Nat, da: Nat, db: Nat,
                     +num: Nat, +den: Nat, +win: Nat,
                     h: {Nat.is_lt(da, db) == True{} : Bool},
                     hb: R.le_ok(db, n))
    -> {Nat.is_ne(R.l_i0(R.route_read(n, da, num, den, win)),
                  R.l_i0(R.route_read(n, db, num, den, win))) == True{} : Bool}:
  match da db h hb:
    case 0n 0n h hb:
      Bool.fne({Nat.is_ne(R.l_i0(R.route_read(n, 0n, num, den, win)),
                          R.l_i0(R.route_read(n, 0n, num, den, win)))
                == True{} : Bool}, h)
    case 0n 1n+dq h hb:
      clamp_distinct_go(n, dq, hb)
    case 1n+dap 0n h hb:
      Bool.fne({Nat.is_ne(R.l_i0(R.route_read(n, 1n+dap, num, den, win)),
                          R.l_i0(R.route_read(n, 0n, num, den, win)))
                == True{} : Bool}, h)
    case 1n+dap 1n+dq h hb:
      delay_inj_go(n, 1n+dap, 1n+dq, h, hb)
def Laws.read_distinct(n, da, db, num, den, win, h, hb):
  read_distinct_go(n, da, db, num, den, win, h, hb)

# i0_win_irrelevant: both i0s reduce to the same normal form (the d match
# answers i0 before win is ever touched), so it is reflexivity.
def i0_win_irrelevant_go(+n: Nat, +d: Nat, +num: Nat, +den: Nat,
                          +wa: Nat, +wb: Nat)
    -> {R.l_i0(R.route_read(n, d, num, den, wa))
        == R.l_i0(R.route_read(n, d, num, den, wb)) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+dp:
      {==}
def Laws.i0_win_irrelevant(n, d, num, den, wa, wb):
  i0_win_irrelevant_go(n, d, num, den, wa, wb)

# route_distinct: both projections read the same source lane, so pb's
# source can be substituted into pa's read (eq_of_is_eq + Equal.sym: the
# rewrite replaces the marked positions with the LEFT side), and then
# read_distinct closes the goal -- the two reads sit at the same n, the
# same lane fraction, and distinct in-horizon delays.  The go wrapper
# carries +pa/+pb so each projection can be queried twice (d and win).
def route_distinct_go(+ls: List<&2, R.Lane>, +pa: R.Proj, +pb: R.Proj,
                      hsrc: {Nat.is_eq(R.proj_src(pa), R.proj_src(pb)) == True{} : Bool},
                      h: {Nat.is_lt(R.proj_d(pa), R.proj_d(pb)) == True{} : Bool},
                      hb: R.le_ok(R.proj_d(pb),
                                  R.lane_newest(R.nth_lane(ls, R.proj_src(pb)))))
    -> {Nat.is_ne(R.l_i0(R.route_read(R.lane_newest(R.nth_lane(ls, R.proj_src(pa))),
                                      R.proj_d(pa),
                                      R.lane_num(R.nth_lane(ls, R.proj_src(pa))),
                                      R.lane_k(R.nth_lane(ls, R.proj_src(pa))),
                                      R.proj_win(pa))),
                  R.l_i0(R.route_read(R.lane_newest(R.nth_lane(ls, R.proj_src(pb))),
                                      R.proj_d(pb),
                                      R.lane_num(R.nth_lane(ls, R.proj_src(pb))),
                                      R.lane_k(R.nth_lane(ls, R.proj_src(pb))),
                                      R.proj_win(pb)))) == True{} : Bool}:
  e = Equal.sym(Nat, R.proj_src(pa), R.proj_src(pb),
                eq_of_is_eq_go(R.proj_src(pa), R.proj_src(pb), hsrc))
  %e : {Nat.is_ne(R.l_i0(R.route_read(R.lane_newest(R.nth_lane(ls, _)),
                                      R.proj_d(pa),
                                      R.lane_num(R.nth_lane(ls, _)),
                                      R.lane_k(R.nth_lane(ls, _)),
                                      R.proj_win(pa))),
                  R.l_i0(R.route_read(R.lane_newest(R.nth_lane(ls, R.proj_src(pb))),
                                      R.proj_d(pb),
                                      R.lane_num(R.nth_lane(ls, R.proj_src(pb))),
                                      R.lane_k(R.nth_lane(ls, R.proj_src(pb))),
                                      R.proj_win(pb)))) == True{} : Bool}
  # align the windows: the second read's win(pb) becomes win(pa)
  e2 = i0_win_irrelevant_go(R.lane_newest(R.nth_lane(ls, R.proj_src(pb))),
                             R.proj_d(pb),
                             R.lane_num(R.nth_lane(ls, R.proj_src(pb))),
                             R.lane_k(R.nth_lane(ls, R.proj_src(pb))),
                             R.proj_win(pa), R.proj_win(pb))
  %e2 : {Nat.is_ne(R.l_i0(R.route_read(R.lane_newest(R.nth_lane(ls, R.proj_src(pb))),
                                       R.proj_d(pa),
                                       R.lane_num(R.nth_lane(ls, R.proj_src(pb))),
                                       R.lane_k(R.nth_lane(ls, R.proj_src(pb))),
                                       R.proj_win(pa))),
                   _) == True{} : Bool}
  read_distinct_go(R.lane_newest(R.nth_lane(ls, R.proj_src(pb))),
                   R.proj_d(pa), R.proj_d(pb),
                   R.lane_num(R.nth_lane(ls, R.proj_src(pb))),
                   R.lane_k(R.nth_lane(ls, R.proj_src(pb))),
                   R.proj_win(pa),
                   h, hb)
def Laws.route_distinct(ls, pa, pb, hsrc, h, hb):
  route_distinct_go(ls, pa, pb, hsrc, h, hb)


# --------------------------------------------------------------------------
# 5b/5c/5d. the per-index validation, write-uniqueness, window-agreement laws
# --------------------------------------------------------------------------

# ok_proj_shape_nth: induction on ps, peeling i.  i=0 reads the head, whose
# proj_shape_ok is the head conjunct of the fold; i=1+q recurses into the
# tail with the tail conjunct.  The Nil case is absurd (i < 0).
def projs_shape_ok_nth_go(+nlanes: Nat, +horizon: Nat, +ps: List<&2, R.Proj>,
                          i: Nat, h: R.lt_ok(i, R.projs_len(ps)),
                          hok: {R.projs_shape_ok(nlanes, horizon, ps) == True{} : Bool})
    -> {R.proj_shape_ok(nlanes, horizon, R.nth_proj(ps, i)) == True{} : Bool}:
  match ps i h:
    case Nil{} _ h:
      Empty.absurd({R.proj_shape_ok(nlanes, horizon, R.nth_proj(Nil{}, i)) == True{} : Bool},
                   lt_ok_nil_absurd(i, h))
    case p <> t 0n _:
      and_elim_l_go(R.proj_shape_ok(nlanes, horizon, p),
                    R.projs_shape_ok(nlanes, horizon, t), hok)
    case p <> t 1n+q hlt:
      projs_shape_ok_nth_go(nlanes, horizon, t, q, hlt,
                            and_elim_r_go(R.proj_shape_ok(nlanes, horizon, p),
                                          R.projs_shape_ok(nlanes, horizon, t), hok))
def Laws.ok_proj_shape_nth(nlanes, horizon, ps, i, h, hok):
  projs_shape_ok_nth_go(nlanes, horizon, ps, i, h, hok)

# ok_fits_nth: proj_shape_ok at index i, then fits_lt's brick.
def ok_fits_nth_go(+nlanes: Nat, +horizon: Nat, +ps: List<&2, R.Proj>, +i: Nat,
                   h: R.lt_ok(i, R.projs_len(ps)),
                   hok: {R.projs_shape_ok(nlanes, horizon, ps) == True{} : Bool})
    -> {Nat.is_lt(R.proj_d(R.nth_proj(ps, i)), horizon) == True{} : Bool}:
  lt_of_le_succ_go(R.proj_d(R.nth_proj(ps, i)), horizon,
                   proj_delay_fits_go(nlanes, horizon, R.nth_proj(ps, i),
                                      projs_shape_ok_nth_go(nlanes, horizon, ps, i, h, hok)))
def Laws.ok_fits_nth(nlanes, horizon, ps, i, h, hok):
  ok_fits_nth_go(nlanes, horizon, ps, i, h, hok)

# lanes_nth_valid: same induction shape on the Nat list.
def lanes_nth_valid_go(+ks: List<&2, Nat>, i: Nat, h: R.lt_ok(i, R.nats_len(ks)),
                       hok: {R.lanes_ok(ks) == True{} : Bool})
    -> {Nat.is_ge(R.nats_nth(ks, i), 1n) == True{} : Bool}:
  match ks i h:
    case Nil{} _ h:
      Empty.absurd({Nat.is_ge(R.nats_nth(Nil{}, i), 1n) == True{} : Bool},
                   lt_ok_nil_absurd(i, h))
    case k <> t 0n _:
      and_elim_l_go(Nat.is_ge(k, 1n), R.lanes_ok(t), hok)
    case k <> t 1n+q hlt:
      lanes_nth_valid_go(t, q, hlt,
                         and_elim_r_go(Nat.is_ge(k, 1n), R.lanes_ok(t), hok))
def Laws.lanes_nth_valid(ks, i, h, hok):
  lanes_nth_valid_go(ks, i, h, hok)

# csr_nth_delay_fits / csr_nth_index_bound: csr_ok's last two conjuncts are
# nats_lt_all folds; peel them to the per-index form by induction on the
# delays/indices list, i peeling in lockstep.
def csr_nth_delay_go(+horizon: Nat, +ds: List<&2, Nat>, i: Nat,
                     h: R.lt_ok(i, R.nats_len(ds)),
                     hall: {R.nats_lt_all(horizon, ds) == True{} : Bool})
    -> {Nat.is_lt(R.nats_nth(ds, i), horizon) == True{} : Bool}:
  match ds i h:
    case Nil{} _ h:
      Empty.absurd({Nat.is_lt(R.nats_nth(Nil{}, i), horizon) == True{} : Bool},
                   lt_ok_nil_absurd(i, h))
    case d <> t 0n _:
      and_elim_l_go(Nat.is_lt(d, horizon), R.nats_lt_all(horizon, t), hall)
    case d <> t 1n+q hlt:
      csr_nth_delay_go(horizon, t, q, hlt,
                       and_elim_r_go(Nat.is_lt(d, horizon), R.nats_lt_all(horizon, t), hall))

def csr_nth_index_go(+nsrc: Nat, +xs: List<&2, Nat>, i: Nat,
                     h: R.lt_ok(i, R.nats_len(xs)),
                     hall: {R.nats_lt_all(nsrc, xs) == True{} : Bool})
    -> {Nat.is_lt(R.nats_nth(xs, i), nsrc) == True{} : Bool}:
  match xs i h:
    case Nil{} _ h:
      Empty.absurd({Nat.is_lt(R.nats_nth(Nil{}, i), nsrc) == True{} : Bool},
                   lt_ok_nil_absurd(i, h))
    case x <> t 0n _:
      and_elim_l_go(Nat.is_lt(x, nsrc), R.nats_lt_all(nsrc, t), hall)
    case x <> t 1n+q hlt:
      csr_nth_index_go(nsrc, t, q, hlt,
                       and_elim_r_go(Nat.is_lt(x, nsrc), R.nats_lt_all(nsrc, t), hall))

# peel csr_ok's five conjuncts down to the two nats_lt_all folds, one
# and_elim_r_go per layer (the same stepped style as proj_win_fits_go)
def csr_ok_delays_go(+nsrc: Nat, +horizon: Nat, +c: R.Csr,
                     hok: {R.csr_ok(nsrc, horizon, c) == True{} : Bool})
    -> {R.nats_lt_all(horizon, R.csr_delays(c)) == True{} : Bool}:
  h1 = and_elim_r_go(R.csr_first_zero(R.csr_indptr(c)),
                     Bool.and(R.csr_sorted(R.csr_indptr(c)),
                              Bool.and(Nat.is_eq(R.nats_last(R.csr_indptr(c)), R.nats_len(R.csr_indices(c))),
                                       Bool.and(Nat.is_eq(R.nats_len(R.csr_indices(c)), R.nats_len(R.csr_delays(c))),
                                                Bool.and(R.nats_lt_all(nsrc, R.csr_indices(c)),
                                                         R.nats_lt_all(horizon, R.csr_delays(c)))))),
                     hok)
  h2 = and_elim_r_go(R.csr_sorted(R.csr_indptr(c)),
                     Bool.and(Nat.is_eq(R.nats_last(R.csr_indptr(c)), R.nats_len(R.csr_indices(c))),
                              Bool.and(Nat.is_eq(R.nats_len(R.csr_indices(c)), R.nats_len(R.csr_delays(c))),
                                       Bool.and(R.nats_lt_all(nsrc, R.csr_indices(c)),
                                                R.nats_lt_all(horizon, R.csr_delays(c))))),
                     h1)
  h3 = and_elim_r_go(Nat.is_eq(R.nats_last(R.csr_indptr(c)), R.nats_len(R.csr_indices(c))),
                     Bool.and(Nat.is_eq(R.nats_len(R.csr_indices(c)), R.nats_len(R.csr_delays(c))),
                              Bool.and(R.nats_lt_all(nsrc, R.csr_indices(c)),
                                       R.nats_lt_all(horizon, R.csr_delays(c)))),
                     h2)
  h4 = and_elim_r_go(Nat.is_eq(R.nats_len(R.csr_indices(c)), R.nats_len(R.csr_delays(c))),
                     Bool.and(R.nats_lt_all(nsrc, R.csr_indices(c)),
                              R.nats_lt_all(horizon, R.csr_delays(c))),
                     h3)
  and_elim_r_go(R.nats_lt_all(nsrc, R.csr_indices(c)),
                R.nats_lt_all(horizon, R.csr_delays(c)), h4)

def csr_ok_indices_go(+nsrc: Nat, +horizon: Nat, +c: R.Csr,
                      hok: {R.csr_ok(nsrc, horizon, c) == True{} : Bool})
    -> {R.nats_lt_all(nsrc, R.csr_indices(c)) == True{} : Bool}:
  h1 = and_elim_r_go(R.csr_first_zero(R.csr_indptr(c)),
                     Bool.and(R.csr_sorted(R.csr_indptr(c)),
                              Bool.and(Nat.is_eq(R.nats_last(R.csr_indptr(c)), R.nats_len(R.csr_indices(c))),
                                       Bool.and(Nat.is_eq(R.nats_len(R.csr_indices(c)), R.nats_len(R.csr_delays(c))),
                                                Bool.and(R.nats_lt_all(nsrc, R.csr_indices(c)),
                                                         R.nats_lt_all(horizon, R.csr_delays(c)))))),
                     hok)
  h2 = and_elim_r_go(R.csr_sorted(R.csr_indptr(c)),
                     Bool.and(Nat.is_eq(R.nats_last(R.csr_indptr(c)), R.nats_len(R.csr_indices(c))),
                              Bool.and(Nat.is_eq(R.nats_len(R.csr_indices(c)), R.nats_len(R.csr_delays(c))),
                                       Bool.and(R.nats_lt_all(nsrc, R.csr_indices(c)),
                                                R.nats_lt_all(horizon, R.csr_delays(c))))),
                     h1)
  h3 = and_elim_r_go(Nat.is_eq(R.nats_last(R.csr_indptr(c)), R.nats_len(R.csr_indices(c))),
                     Bool.and(Nat.is_eq(R.nats_len(R.csr_indices(c)), R.nats_len(R.csr_delays(c))),
                              Bool.and(R.nats_lt_all(nsrc, R.csr_indices(c)),
                                       R.nats_lt_all(horizon, R.csr_delays(c)))),
                     h2)
  and_elim_l_go(R.nats_lt_all(nsrc, R.csr_indices(c)),
                R.nats_lt_all(horizon, R.csr_delays(c)),
                and_elim_r_go(Nat.is_eq(R.nats_len(R.csr_indices(c)), R.nats_len(R.csr_delays(c))),
                              Bool.and(R.nats_lt_all(nsrc, R.csr_indices(c)),
                                       R.nats_lt_all(horizon, R.csr_delays(c))),
                              h3))

def Laws.csr_nth_delay_fits(nsrc, horizon, c, i, h, hok):
  csr_nth_delay_go(horizon, R.csr_delays(c), i, h,
                   csr_ok_delays_go(nsrc, horizon, c, hok))

def Laws.csr_nth_index_bound(nsrc, horizon, c, i, h, hok):
  csr_nth_index_go(nsrc, R.csr_indices(c), i, h,
                   csr_ok_indices_go(nsrc, horizon, c, hok))

# clash_split: proj_clash is the AND of the two deciders; refine it by
# casing on tgt-eq (given True by ht) and tc-eq.  If tc were also equal
# the AND would be True and Bool.not of it False, contradicting hn; so
# the tc-decider must be False, and is_ne of equal Nats is exactly that.
# the decider pair, each computed once and passed as its own parameter so
# the match can refine (Bend matches only on parameters, not computed terms)
def proj_tgt_eq(+pa: R.Proj, +pb: R.Proj) -> Bool:
  Nat.is_eq(R.proj_tgt(pa), R.proj_tgt(pb))

def proj_tc_eq(+pa: R.Proj, +pb: R.Proj) -> Bool:
  Nat.is_eq(R.proj_tc(pa), R.proj_tc(pb))

def clash_split_arm(+pa: R.Proj, +pb: R.Proj, +tgt: Bool, +tc: Bool,
                    hn: {Bool.not(Bool.and(tgt, tc)) == True{} : Bool},
                    ht: {tgt == True{} : Bool})
    -> {Bool.not(tc) == True{} : Bool}:
  match tgt tc hn:
    case True{} True{} hn:
      Bool.fne({Bool.not(True{}) == True{} : Bool}, hn)
    case True{} False{} _:
      {==}
    case False{} _ _:
      Bool.fne({Bool.not(tc) == True{} : Bool},
               Bool.fne({False{} == True{} : Bool}, ht))

def clash_split_go(+pa: R.Proj, +pb: R.Proj,
                   hn: {Bool.not(R.proj_clash(pa, pb)) == True{} : Bool},
                   ht: {Nat.is_eq(R.proj_tgt(pa), R.proj_tgt(pb)) == True{} : Bool})
    -> {Nat.is_ne(R.proj_tc(pa), R.proj_tc(pb)) == True{} : Bool}:
  clash_split_arm(pa, pb, proj_tgt_eq(pa, pb), proj_tc_eq(pa, pb), hn, ht)

def Laws.clash_split(pa, pb, hn, ht):
  clash_split_go(pa, pb, hn, ht)

# no_clash_nth: induction on ps peeling i -- the head conjunct at i=0,
# the recursive fold at i=1+q.
def no_clash_nth_go(+pa: R.Proj, +ps: List<&2, R.Proj>, i: Nat,
                    h: R.lt_ok(i, R.projs_len(ps)),
                    hnc: {R.no_clash(pa, ps) == True{} : Bool})
    -> {Bool.not(R.proj_clash(pa, R.nth_proj(ps, i))) == True{} : Bool}:
  match ps i h:
    case Nil{} _ h:
      Empty.absurd({Bool.not(R.proj_clash(pa, R.nth_proj(Nil{}, i))) == True{} : Bool},
                   lt_ok_nil_absurd(i, h))
    case p <> t 0n _:
      and_elim_l_go(Bool.not(R.proj_clash(pa, p)), R.no_clash(pa, t), hnc)
    case p <> t 1n+q hlt:
      no_clash_nth_go(pa, t, q, hlt,
                      and_elim_r_go(Bool.not(R.proj_clash(pa, p)), R.no_clash(pa, t), hnc))
def Laws.no_clash_nth(pa, ps, i, h, hnc):
  no_clash_nth_go(pa, ps, i, h, hnc)

# ok_no_clash: double-index induction on (ia, ib) with ia < ib.  Peel ia:
#   ia=0: ib=1+q' lives in the tail; writes_unique's head conjunct is
#          no_clash(head, tail), so no_clash_nth at ib-1 in the TAIL gives
#          clash-free(head, nth(tail, ib-1)) = clash-free(nth(ps,0) vs nth(ps,ib)).
#   ia=1+q: both live in the tail, which is writes_unique itself.
# the ia=0, ib=1+q case: the head clashes with nothing in the tail
# (writes_unique's head conjunct), and clash_split turns that plus the
# target equality into the slot disequality.  +q so it can appear both
# in the nth_proj and the no_clash_nth_go index.
def ok_no_clash_head_go(+p: R.Proj, +t: List<&2, R.Proj>, +q: Nat,
                        hb: R.lt_ok(q, R.projs_len(t)),
                        hu: {R.writes_unique(p <> t) == True{} : Bool},
                        ht: {Nat.is_eq(R.proj_tgt(p), R.proj_tgt(R.nth_proj(t, q))) == True{} : Bool})
    -> {Nat.is_ne(R.proj_tc(p), R.proj_tc(R.nth_proj(t, q))) == True{} : Bool}:
  clash_split_go(p, R.nth_proj(t, q),
                no_clash_nth_go(p, t, q, hb,
                                and_elim_l_go(R.no_clash(p, t), R.writes_unique(t), hu)),
                ht)

def ok_no_clash_go(+ps: List<&2, R.Proj>, ia: Nat, ib: Nat,
                   hltb: {Nat.is_lt(ia, ib) == True{} : Bool},
                   ha: R.lt_ok(ia, R.projs_len(ps)),
                   hb: R.lt_ok(ib, R.projs_len(ps)),
                   hu: {R.writes_unique(ps) == True{} : Bool},
                   ht: {Nat.is_eq(R.proj_tgt(R.nth_proj(ps, ia)),
                                  R.proj_tgt(R.nth_proj(ps, ib))) == True{} : Bool})
    -> {Nat.is_ne(R.proj_tc(R.nth_proj(ps, ia)),
                  R.proj_tc(R.nth_proj(ps, ib))) == True{} : Bool}:
  match ps ia ha:
    case Nil{} _ h:
      Empty.absurd({Nat.is_ne(R.proj_tc(R.nth_proj(Nil{}, ia)),
                              R.proj_tc(R.nth_proj(Nil{}, ib))) == True{} : Bool},
                   lt_ok_nil_absurd(ia, h))
    case p <> t 0n _:
      match ib:
        case 0n:
          Bool.fne({Nat.is_ne(R.proj_tc(p), R.proj_tc(p)) == True{} : Bool},
                   Bool.fne({Nat.is_lt(0n, 0n) == True{} : Bool}, hltb))
        case 1n+q:
          ok_no_clash_head_go(p, t, q, hb, hu, ht)
    case p <> t 1n+q hlt:
      match ib:
        case 0n:
          Bool.fne({Nat.is_ne(R.proj_tc(R.nth_proj(t, q)), R.proj_tc(p)) == True{} : Bool},
                   Bool.fne({Nat.is_lt(1n+q, 0n) == True{} : Bool}, hltb))
        case 1n+r:
          ok_no_clash_go(t, q, r, hltb, hlt, hb,
                         and_elim_r_go(R.no_clash(p, t), R.writes_unique(t), hu),
                         ht)
def Laws.ok_no_clash(ps, ia, ib, hltb, ha, hb, hu, ht):
  ok_no_clash_go(ps, ia, ib, hltb, ha, hb, hu, ht)

# read_i0_is_window_head: both sides reduce to n-d.  At d=0 the clamp
# sets i0 = n and hi = n-0 = n; at d = 1+dp both are n-(1+dp).  Pure
# reflexivity after the d split (the sub is stuck on abstract n, so the
# split is needed to expose the identical normal forms).
def Laws.read_i0_is_window_head(n, d, num, den, win):
  match d:
    case 0n:
      Laws.sub_zero_r(n)
    case 1n+dp:
      {==}

# --------------------------------------------------------------------------
# 6. the tape laws (hist.bend): read-after-write, stability, IC, prune-shift
# --------------------------------------------------------------------------

# hist_read_snoc: reading at the OLD length after a snoc.  Induction on
# xs.  The Nil case is definitional ({v} <> Nil{} read at 0n is v); the
# Cons case peels: the read walks into the tail while the length drops by
# one, so the IH at (p, ic) closes it.
def hist_read_snoc_go(+xs: List<&2, F32>, +v: F32, +ic: F32)
  -> {H.hist_read(H.hist_snoc(xs, v), H.hist_len(xs), ic) == v : F32}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %hist_read_snoc_go(t, v, ic)
        : {H.hist_read(H.hist_snoc(t, v), H.hist_len(t), ic) == _ : F32}
      {==}

def Laws.hist_read_snoc(xs, v, ic):
  hist_read_snoc_go(xs, v, ic)

# hist_snoc_stable: a read below the top is unchanged by the snoc.  The
# witness lt_ok(i, len) refines with i: i=0 reads the head (both sides
# reduce to the same cell); i=1+p recurses into the tail with the
# refined witness.  The IC parameter is shared, untouched.
def hist_snoc_stable_go(+xs: List<&2, F32>, +v: F32, +ic: F32, i: Nat,
                        h: R.lt_ok(i, H.hist_len(xs)))
  -> {H.hist_read(H.hist_snoc(xs, v), i, ic)
      == H.hist_read(xs, i, ic) : F32}:
  match xs i h:
    case Nil{} _ h:
      Empty.absurd({H.hist_read(H.hist_snoc(Nil{}, v), i, ic)
                    == H.hist_read(Nil{}, i, ic) : F32},
                   lt_ok_nil_absurd(i, h))
    case h <> t 0n _:
      {==}
    case h <> t 1n+p hlt:
      hist_snoc_stable_go(t, v, ic, p, hlt)

def Laws.hist_snoc_stable(xs, v, ic, i, h):
  hist_snoc_stable_go(xs, v, ic, i, h)

# hist_read_ic: at or past the length, the read answers the IC fill.
# Induction on xs with the witness le_ok(len, i): Nil is definitional;
# Cons refines the witness to le_ok on the tail's length.
# le_ok(1 + len(t), 0n) is Empty definitionally (the successor case of
# le_ok), so a Cons whose witness forces i = 0n is absurd
def le_ok_cons_absurd(+h: F32, +t: List<&2, F32>,
                      hle: R.le_ok(Nat.add(1n, H.hist_len(t)), 0n)) -> Empty:
  match h t hle:
    case _ _ hle:
      hle

def hist_read_ic_go(+xs: List<&2, F32>, +ic: F32, i: Nat,
                    h: R.le_ok(H.hist_len(xs), i))
  -> {H.hist_read(xs, i, ic) == ic : F32}:
  match xs i h:
    case Nil{} _ _:
      {==}
    case h <> t 0n hle:
      Empty.absurd({H.hist_read(h <> t, 0n, ic) == ic : F32},
                   le_ok_cons_absurd(h, t, hle))
    case h <> t 1n+p hle:
      hist_read_ic_go(t, ic, p, hle)

def Laws.hist_read_ic(xs, ic, i, h):
  hist_read_ic_go(xs, ic, i, h)

# hist_prune_shift: dropping k reindexes by exactly k, unconditionally --
# past the end both sides answer ic, so no witness is needed.  Induction
# on xs and k together; i is never destructed (it is passed whole to the
# recursive call, so no lt_ok refinement is needed either).
def hist_prune_shift_go(+xs: List<&2, F32>, k: Nat, +ic: F32, i: Nat)
  -> {H.hist_read(H.hist_drop(xs, k), i, ic)
      == H.hist_read(xs, Nat.add(k, i), ic) : F32}:
  match xs k:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+q:
      %hist_prune_shift_go(t, q, ic, i)
        : {H.hist_read(H.hist_drop(t, q), i, ic) == _ : F32}
      {==}

def Laws.hist_prune_shift(xs, k, ic, i):
  hist_prune_shift_go(xs, k, ic, i)

# --------------------------------------------------------------------------
# 6b. the ring bridge: mod_lt (the fence), ring_first_lap
# --------------------------------------------------------------------------
# The fence is where the deferred div/mod debt is paid, once.  The go
# countdown consumes n one tick at a time while m decrements; a wrap
# needs a tick with m = 0, which only the (m+2)-th tick sees, so no wrap
# happens exactly while n <= m -- stated in the refination-friendly
# shape lt_ok(n, 1n+m), which peels one level per go step and so makes
# the whole thing a single lockstep induction (the witness IS the
# fence).

# the fence's unsatisfiable case: n a successor with countdown m = 0 is
# below the fence only if p+1 <= 0, which is Empty once p is destructed.
def mod_lt_r_absurd(p: Nat, h: R.le_ok(Nat.add(p, 1n), 0n)) -> Empty:
  match p h:
    case 0n h:
      h
    case 1n+q h:
      h

# the countdown lemma: below the fence the remainder is exactly r + n.
# Base: n = 0, the go returns (d, r) and r == r + 0.  The n > 0, m = 0
# case is Empty (the witness refines to it: n <= m = 0 with n a
# successor is unsatisfiable).  Step: go(1+p, 1+mp, d, r) steps to
# go(p, mp, d, 1+r), the witness to lt_ok(p, 1+mp), and the sum's
# regrouping is add_succ.
def mod_lt_r(n: Nat, m: Nat, +d: Nat, +r: Nat, h: R.lt_ok(n, 1n+m))
  -> {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)) == Nat.add(r, n) : Nat}:
  match n m h:
    case 0n _ _:
      Equal.sym(Nat, Nat.add(r, 0n), r, Laws.add_zero(r))
    case 1n++p 0n h:
      Empty.absurd({Pair.snd(Nat, Nat, Nat.divmod.go(p, r, 1n+d, 0n))
                    == Nat.add(r, 1n+p) : Nat},
                   mod_lt_r_absurd(p, h))
    case 1n+p 1n+mp hle:
      Equal.trans(Nat,
        Pair.snd(Nat, Nat, Nat.divmod.go(p, mp, d, 1n+r)),
        1n+Nat.add(r, p),
        Nat.add(r, 1n+p),
        mod_lt_r(p, mp, d, 1n+r, hle),
        Equal.sym(Nat, Nat.add(r, 1n+p), 1n+Nat.add(r, p),
                  Laws.add_succ(r, p)))

# cap = 0 is absurd: lt_ok(i, 0n) is le_ok(i+1, 0n), which is Empty once
# i is destructed (either case of i reduces the le_ok match).
def mod_lt_zero_absurd(i: Nat, h: R.lt_ok(i, 0n)) -> Empty:
  match i h:
    case 0n h:
      h
    case 1n+p h:
      h

# mod_lt: i < cap forces i mod cap == i -- the first lap is exact.
# cap = 1n+cp puts divmod in the go form with countdown cp, and the
# witness lt_ok(i, 1n+cp) is EXACTLY the fence the countdown lemma
# takes; its result Nat.add(0n, i) reduces to i.
def Laws.mod_lt(i, cap, h):
  match cap h:
    case 0n h:
      Empty.absurd({Nat.mod(i, 0n) == i : Nat},
                   mod_lt_zero_absurd(i, h))
    case 1n+cp hlt:
      mod_lt_r(i, cp, 0n, 0n, hlt)

# ring_first_lap: below the fence the ring read IS the tape read at the
# same absolute index -- the mod is the identity there (mod_lt), so
# Design B and Design A agree slot for slot everywhere lt_ok(i, cap).
def Laws.ring_first_lap(xs, i, cap, ic, h):
  Equal.cong(Nat, F32, z => H.hist_read(xs, z, ic),
             Nat.mod(i, cap), i, Laws.mod_lt(i, cap, h))
