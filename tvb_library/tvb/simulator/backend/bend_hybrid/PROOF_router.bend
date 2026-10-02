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
