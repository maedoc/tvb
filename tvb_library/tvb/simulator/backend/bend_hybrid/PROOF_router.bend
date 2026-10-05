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

# --------------------------------------------------------------------------
# 6c. the blend wiring laws: blend_adjacent, clamp_reads_same,
#     clamp_zero_frac
# --------------------------------------------------------------------------
# The interpolation's operands are exactly the router's two cells.
# d = 0: the clamp makes both cells n and the numerator 0, so the blend
# reads the newest sample twice with alpha = 0 -- pure {==} refinement,
# no induction at all.  d = 1+dp: the endpoints are adjacent ticks,
# i.e. sub(n, dp) == sub(n, 1+dp) + 1.  The witness le_ok(1+dp, n)
# refines with n: n = 0 is unsatisfiable (needs a destructed dp), and
# n = 1+np turns it into le_ok(dp, np), which feeds sub_succ_l's Bool
# hypothesis via le_ok_iff; the remaining regrouping is add_one.

# the n = 0 case is unsatisfiable: le_ok(1+dp, 0n) is Empty once dp is
# destructed (either shape of dp reduces the le_ok match).
def blend_adj_zero_absurd(dp: Nat, h: R.le_ok(Nat.add(1n, dp), 0n)) -> Empty:
  match dp h:
    case 0n h:
      h
    case 1n+q h:
      h

# adjacency: for an in-history delay the blend's two reads are exactly
# one tick apart -- the interpolation never bridges a gap wider than 1.
def blend_adjacent_go(+n: Nat, +dp: Nat, num: Nat, den: Nat, win: Nat,
  h: R.le_ok(Nat.add(1n, dp), n))
  -> {R.l_i1(R.route_read(n, 1n+dp, num, den, win))
    == Nat.add(R.l_i0(R.route_read(n, 1n+dp, num, den, win)), 1n) : Nat}:
  match n h:
    case 0n h:
      Empty.absurd({R.l_i1(R.route_read(0n, 1n+dp, num, den, win))
                    == Nat.add(R.l_i0(R.route_read(0n, 1n+dp, num, den, win)), 1n) : Nat},
                   blend_adj_zero_absurd(dp, h))
    case 1n+np hle:
      Equal.trans(Nat,
        Nat.sub(1n+np, dp),
        Nat.add(1n, Nat.sub(np, dp)),
        Nat.add(Nat.sub(1n+np, 1n+dp), 1n),
        Laws.sub_succ_l(np, dp, Laws.le_ok_iff(dp, np, hle)),
        Laws.add_comm(1n, Nat.sub(np, dp)))

def Laws.blend_adjacent(n, dp, num, den, win, h):
  blend_adjacent_go(n, dp, num, den, win, h)

# the clamp collapses both operands onto the newest cell: with d = 0,
# route_read is Line{n, n, 0n, den, win}, so both hist_reads are the
# same index definitionally.
def Laws.clamp_reads_same(tape, n, num, den, win, ic):
  {==}

# the clamp zeroes the fraction: the numerator is 0n definitionally, so
# alpha = 0.0 and the blend adds zero times the (bogus) delta.
def Laws.clamp_zero_frac(n, num, den, win):
  {==}

# --------------------------------------------------------------------------
# 6d. the CSR slice laws (Link 3)
# --------------------------------------------------------------------------
# take_nth: induction on the witness lt_ok(i, k), peeling one level of
# both i and k per step.  Base: k = 0 is absurd (i < 0).  Step: take
# keeps the head, so i = 0 is definitional; i = 1+p recurses into the
# tail with witness lt_ok(p, q).
def take_nth_go(+xs: List<&2, Nat>, k: Nat, i: Nat,
  h: R.lt_ok(i, k))
  -> {R.nats_nth(R.nats_take(xs, k), i) == R.nats_nth(xs, i) : Nat}:
  match xs k i h:
    case Nil{} _ _ _:
      {==}
    case _ 0n _ h:
      Empty.absurd({R.nats_nth(R.nats_take(xs, 0n), i) == R.nats_nth(xs, i) : Nat},
                   mod_lt_zero_absurd(i, h))
    case _ 1n+q 0n _:
      {==}
    case h <> t 1n+q 1n+p hlt:
      take_nth_go(t, q, p, hlt)

def Laws.take_nth(xs, k, i, h):
  take_nth_go(xs, k, i, h)

# drop_nth: the drop's mirror -- reading drop(xs, lo) at i (i < len - lo
# not needed; nth's default-past-end makes it unconditional) is reading
# xs at lo + i.  This is the composition step of slice_nth: the slice is
# take(drop(xs, lo), hi - lo).
def drop_nth_go(+xs: List<&2, Nat>, lo: Nat, i: Nat)
  -> {R.nats_nth(R.nats_drop(xs, lo), i) == R.nats_nth(xs, Nat.add(lo, i)) : Nat}:
  match xs lo:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+q:
      drop_nth_go(t, q, i)

def drop_nth(xs: List<&2, Nat>, lo: Nat, i: Nat)
  -> {R.nats_nth(R.nats_drop(xs, lo), i) == R.nats_nth(xs, Nat.add(lo, i)) : Nat}:
  drop_nth_go(xs, lo, i)

# slice_nth: composition -- the slice read at i is take(drop(xs, lo), w)
# read at i, which is drop(xs, lo) at i (take_nth, witness lt_ok(i, w)),
# which is xs at lo + i (drop_nth).  The regrouping lo + (lo' + i) is
# NOT needed: drop_nth's lo is exactly the slice's lo.
def slice_nth_go(+xs: List<&2, Nat>, +lo: Nat, +hi: Nat, +i: Nat,
  h: R.lt_ok(i, Nat.sub(hi, lo)))
  -> {R.nats_nth(R.nats_slice(xs, lo, hi), i)
    == R.nats_nth(xs, Nat.add(lo, i)) : Nat}:
  Equal.trans(Nat,
    R.nats_nth(R.nats_slice(xs, lo, hi), i),
    R.nats_nth(R.nats_drop(xs, lo), i),
    R.nats_nth(xs, Nat.add(lo, i)),
    Laws.take_nth(R.nats_drop(xs, lo), Nat.sub(hi, lo), i, h),
    drop_nth(xs, lo, i))

def Laws.slice_nth(xs, lo, hi, i, h):
  slice_nth_go(xs, lo, hi, i, h)

# take_len: take never grows the list past k -- the length bound of the
# fold's input.  Structural induction on the list; the k = 0 case is
# definitional (Nil), and a Nil tail makes len 0 <= anything.
def take_len_go(+xs: List<&2, Nat>, k: Nat)
  -> {Nat.is_le(R.nats_len(R.nats_take(xs, k)), k) == True{} : Bool}:
  match xs k:
    case Nil{} _:
      le_zero(k)
    case _ 0n:
      {==}
    case h <> t 1n+q:
      take_len_go(t, q)

def take_len(xs: List<&2, Nat>, k: Nat)
  -> {Nat.is_le(R.nats_len(R.nats_take(xs, k)), k) == True{} : Bool}:
  take_len_go(xs, k)

# drop_len: dropping shrinks or keeps the length -- the other half of
# the slice's length bound.
def drop_len_nil_go(k: Nat)
  -> {Nat.is_le(R.nats_len(R.nats_drop(Nil{}, k)), 0n) == True{} : Bool}:
  {==}

def drop_len_go(+xs: List<&2, Nat>, +k: Nat)
  -> {Nat.is_le(R.nats_len(R.nats_drop(xs, k)), R.nats_len(xs)) == True{} : Bool}:
  match xs k:
    case Nil{} _:
      drop_len_nil_go(k)
    case _ 0n:
      Laws.le_refl_b(R.nats_len(xs))
    case h <> t 1n+q:
      Laws.le_succ_of_le(R.nats_len(R.nats_drop(t, q)), R.nats_len(t),
        drop_len_go(t, q))

def drop_len(xs: List<&2, Nat>, k: Nat)
  -> {Nat.is_le(R.nats_len(R.nats_drop(xs, k)), R.nats_len(xs)) == True{} : Bool}:
  drop_len_go(xs, k)

# slice_len: transitivity -- the slice is take(drop(xs, lo), hi - lo),
# its length is <= hi - lo by take_len directly (the drop underneath
# only shrinks the input, which take_len is independent of).
def slice_len_go(+xs: List<&2, Nat>, +lo: Nat, +hi: Nat)
  -> {Nat.is_le(R.nats_len(R.nats_slice(xs, lo, hi)), Nat.sub(hi, lo))
    == True{} : Bool}:
  take_len(R.nats_drop(xs, lo), Nat.sub(hi, lo))

def Laws.slice_len(xs, lo, hi):
  slice_len_go(xs, lo, hi)

# the positive instances: pure computation, definitional.
def Laws.csr_row_good_0():
  {==}

def Laws.csr_row_good_1():
  {==}

def Laws.csr_row_delays_good_1():
  {==}

# --------------------------------------------------------------------------
# 6e. the end-to-end capstone (Link 4)
# --------------------------------------------------------------------------
# row_lines_nth: induction on the row width, peeling one edge per step.
# The table is edge_lines_from(ls, ixs, ds, w, lo) with w = hi - lo:
# at j = 0 the head IS the edge at flat index lo (definitional -- both
# sides read nth(ixs, lo), nth(ds, lo)); at j = 1+p the tail continues
# from flat index lo + 1 with width q, and the flat reads regroup
# lo + (1 + p) == (1 + lo) + p via add_assoc/add_comm -- the same move
# as the staleness bound's countdown induction.
def row_lines_nth_go(+ls: List<&2, R.Lane>, +c: R.Csr, +t: Nat,
                     w: Nat, +lo: Nat, +j: Nat,
                     h: R.lt_ok(j, w))
  -> {R.nth_line(R.edge_lines_from(ls, R.csr_indices(c), R.csr_delays(c), w, lo), j)
    == R.edge(ls,
        R.nats_nth(R.csr_indices(c), Nat.add(lo, j)),
        R.nats_nth(R.csr_delays(c), Nat.add(lo, j)))
    : R.Line}:
  match w:
    case 0n:
      match j:
        case 0n:
          Empty.absurd({R.nth_line(R.edge_lines_from(ls, R.csr_indices(c), R.csr_delays(c), 0n, lo), 0n)
            == R.edge(ls, R.nats_nth(R.csr_indices(c), Nat.add(lo, 0n)),
                      R.nats_nth(R.csr_delays(c), Nat.add(lo, 0n))) : R.Line},
            mod_lt_zero_absurd(0n, h))
        case 1n+p:
          Empty.absurd({R.nth_line(R.edge_lines_from(ls, R.csr_indices(c), R.csr_delays(c), 0n, lo), 1n+p)
            == R.edge(ls, R.nats_nth(R.csr_indices(c), Nat.add(lo, 1n+p)),
                      R.nats_nth(R.csr_delays(c), Nat.add(lo, 1n+p))) : R.Line},
            mod_lt_zero_absurd(1n+p, h))
    case 1n+q:
      match j h:
        case 0n _:
          Equal.sym(R.Line,
            R.edge(ls,
              R.nats_nth(R.csr_indices(c), Nat.add(lo, 0n)),
              R.nats_nth(R.csr_delays(c), Nat.add(lo, 0n))),
            R.edge(ls,
              R.nats_nth(R.csr_indices(c), lo),
              R.nats_nth(R.csr_delays(c), lo)),
            Equal.trans(R.Line,
              R.edge(ls,
                R.nats_nth(R.csr_indices(c), Nat.add(lo, 0n)),
                R.nats_nth(R.csr_delays(c), Nat.add(lo, 0n))),
              R.edge(ls,
                R.nats_nth(R.csr_indices(c), lo),
                R.nats_nth(R.csr_delays(c), Nat.add(lo, 0n))),
              R.edge(ls,
                R.nats_nth(R.csr_indices(c), lo),
                R.nats_nth(R.csr_delays(c), lo)),
              Equal.cong(Nat, R.Line,
                z => R.edge(ls, R.nats_nth(R.csr_indices(c), z),
                            R.nats_nth(R.csr_delays(c), Nat.add(lo, 0n))),
                Nat.add(lo, 0n), lo,
                Laws.add_zero(lo)),
              Equal.cong(Nat, R.Line,
                z => R.edge(ls, R.nats_nth(R.csr_indices(c), lo),
                            R.nats_nth(R.csr_delays(c), z)),
                Nat.add(lo, 0n), lo,
                Laws.add_zero(lo))))
        case 1n+p hlt:
          Equal.trans(R.Line,
            R.nth_line(R.edge_lines_from(ls, R.csr_indices(c), R.csr_delays(c), q, Nat.add(lo, 1n)), p),
            R.edge(ls,
              R.nats_nth(R.csr_indices(c), Nat.add(Nat.add(lo, 1n), p)),
              R.nats_nth(R.csr_delays(c), Nat.add(Nat.add(lo, 1n), p))),
            R.edge(ls,
              R.nats_nth(R.csr_indices(c), Nat.add(lo, 1n+p)),
              R.nats_nth(R.csr_delays(c), Nat.add(lo, 1n+p))),
            row_lines_nth_go(ls, c, t, q, Nat.add(lo, 1n), p, hlt),
            Equal.sym(R.Line,
              R.edge(ls,
                R.nats_nth(R.csr_indices(c), Nat.add(lo, 1n+p)),
                R.nats_nth(R.csr_delays(c), Nat.add(lo, 1n+p))),
              R.edge(ls,
                R.nats_nth(R.csr_indices(c), Nat.add(Nat.add(lo, 1n), p)),
                R.nats_nth(R.csr_delays(c), Nat.add(Nat.add(lo, 1n), p))),
              Equal.trans(R.Line,
                R.edge(ls,
                  R.nats_nth(R.csr_indices(c), Nat.add(lo, 1n+p)),
                  R.nats_nth(R.csr_delays(c), Nat.add(lo, 1n+p))),
                R.edge(ls,
                  R.nats_nth(R.csr_indices(c), Nat.add(Nat.add(lo, 1n), p)),
                  R.nats_nth(R.csr_delays(c), Nat.add(lo, 1n+p))),
                R.edge(ls,
                  R.nats_nth(R.csr_indices(c), Nat.add(Nat.add(lo, 1n), p)),
                  R.nats_nth(R.csr_delays(c), Nat.add(Nat.add(lo, 1n), p))),
                Equal.cong(Nat, R.Line,
                  z => R.edge(ls, R.nats_nth(R.csr_indices(c), z),
                              R.nats_nth(R.csr_delays(c), Nat.add(lo, 1n+p))),
                  Nat.add(lo, 1n+p), Nat.add(Nat.add(lo, 1n), p),
                  Equal.sym(Nat, Nat.add(Nat.add(lo, 1n), p), Nat.add(lo, 1n+p),
                    Laws.add_assoc(lo, 1n, p))),
                Equal.cong(Nat, R.Line,
                  z => R.edge(ls, R.nats_nth(R.csr_indices(c), Nat.add(Nat.add(lo, 1n), p)),
                              R.nats_nth(R.csr_delays(c), z)),
                  Nat.add(lo, 1n+p), Nat.add(Nat.add(lo, 1n), p),
                  Equal.sym(Nat, Nat.add(Nat.add(lo, 1n), p), Nat.add(lo, 1n+p),
                    Laws.add_assoc(lo, 1n, p))))))

# w = 0 is absurd at j a successor: lt_ok(1+p, 0n) is Empty.
def row_lines_zero_absurd(p: Nat, h: R.lt_ok(1n+p, 0n)) -> Empty:
  match p h:
    case 0n h:
      h
    case 1n+q h:
      h

def Laws.row_lines_nth(ls, c, t, j, h):
  row_lines_nth_go(ls, c, t, Nat.sub(R.csr_row_hi(c, t), R.csr_row_lo(c, t)),
                   R.csr_row_lo(c, t), j, h)

# row_lines_len: the table has exactly the row's width -- each step of
# edge_lines_from conses one line and shrinks the countdown, so the
# lengths reduce in lockstep.  Induction on the width.
def row_lines_len_go(+ls: List<&2, R.Lane>, +c: R.Csr, w: Nat, +lo: Nat)
  -> {R.lines_len(R.edge_lines_from(ls, R.csr_indices(c), R.csr_delays(c), w, lo))
    == w : Nat}:
  match w:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, z => Nat.add(1n, z),
        R.lines_len(R.edge_lines_from(ls, R.csr_indices(c), R.csr_delays(c), q,
                                      Nat.add(lo, 1n))),
        q,
        row_lines_len_go(ls, c, q, Nat.add(lo, 1n)))

def Laws.row_lines_len(ls, c, t):
  row_lines_len_go(ls, c, Nat.sub(R.csr_row_hi(c, t), R.csr_row_lo(c, t)),
                   R.csr_row_lo(c, t))

# the positive instance: pure computation, definitional.
def Laws.row_lines_good_1():
  {==}

# --------------------------------------------------------------------------
# 7a. the cap >= horizon closure: the capacity gate, the read-window bound
# --------------------------------------------------------------------------

# ok_cap_good / ok_cap_bad: pure computation, definitional
def Laws.ok_cap_good():
  {==}

def Laws.ok_cap_bad():
  {==}

# ok_cap_le: ok_cap unfolds definitionally to the decider, so the
# hypothesis IS the goal.
def Laws.ok_cap_le(c, cap, h):
  h

# saturating sub is antitone unconditionally: sub_le_mono's induction with
# the in-history witness dropped -- no case ever consumed it.
def sub_antitone_go(+n: Nat, +a: Nat, +b: Nat,
                    h: {Nat.is_le(a, b) == True{} : Bool})
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
      sub_antitone_go(p, r, q, h)

def Laws.sub_antitone(n, a, b, h):
  sub_antitone_go(n, a, b, h)

# a < b implies a <= b: the strict decider's True forces the weak one;
# the (1+p, 0) case is absurd (nothing is below 0).
def le_of_lt_go(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool})
    -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b h:
    case 0n b _:
      le_zero(b)
    case 1n+p 0n h:
      Bool.fne({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q h:
      le_of_lt_go(p, q, h)

def Laws.le_of_lt(a, b, h):
  le_of_lt_go(a, b, h)

# read_window_lo: the projection's window fits the horizon (proj_win_fits:
# d + win <= horizon), and cancelling more leaves less-or-equal
# (sub_antitone), so the window's oldest cell n - (d + win) is at or
# behind n - horizon: the horizon is the worst-case read depth.
def Laws.read_window_lo(n, nlanes, horizon, p, h):
  sub_antitone_go(n, Nat.add(R.proj_d(p), R.proj_win(p)), horizon,
                  proj_win_fits_go(nlanes, horizon, p, h))

# csr_window_lo: peel the delays list and the index in lockstep.  In
# bounds: csr_ok's nats_lt_all gives the delay strictly inside the
# horizon, le_of_lt weakens it, sub_antitone orders the depths.  Past the
# end: nats_nth answers 0n and n - 0 == n, which is at or behind n -
# horizon (sub_le_self) -- the default read is the NEWEST sample, the
# most conservative depth there is.
def csr_window_lo_go(+n: Nat, +horizon: Nat, +ds: List<&2, Nat>, i: Nat,
                     hall: {R.nats_lt_all(horizon, ds) == True{} : Bool})
    -> {Nat.is_le(Nat.sub(n, horizon),
                  Nat.sub(n, R.nats_nth(ds, i))) == True{} : Bool}:
  match ds i:
    case Nil{} _:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, Laws.sub_zero_r(n))
        : {Nat.is_le(Nat.sub(n, horizon), _) == True{} : Bool}
      Laws.sub_le_self(n, horizon)
    case +d <> t 0n:
      sub_antitone_go(n, d, horizon,
                      le_of_lt_go(d, horizon,
                                  and_elim_l_go(Nat.is_lt(d, horizon),
                                                R.nats_lt_all(horizon, t),
                                                hall)))
    case d <> t 1n+q:
      csr_window_lo_go(n, horizon, t, q,
                       and_elim_r_go(Nat.is_lt(d, horizon),
                                     R.nats_lt_all(horizon, t),
                                     hall))

def Laws.csr_window_lo(n, nsrc, horizon, c, i, h):
  csr_window_lo_go(n, horizon, R.csr_delays(c), i,
                   csr_ok_delays_go(nsrc, horizon, c, h))

# --------------------------------------------------------------------------

# --------------------------------------------------------------------------
# 7c. the divmod machinery: the twin (mm), the bridge, the splice, the proofs
# --------------------------------------------------------------------------
# The four divmod laws are proved through a STRUCTURAL TWIN of the divmod
# go-machine.  The go-machine
#
#   go(0,    m, d, r) = (d, r)
#   go(1+n,  0, d, r) = go(n, r, 1+d, 0)     -- the wrap
#   go(1+n, 1+m, d, r) = go(n, m, d, 1+r)    -- the normal tick
#
# hides the countdown (m) inside the recursion: after a wrap the OLD SLOT
# becomes the new countdown, but an observer of go's OUTPUT can never see
# it -- the state is existential.  The twin keeps it:
#
#   mm(n, m, r) = (countdown left, slot)          -- a Nat & Nat
#
# with the SAME tick/wrap recursion (the quotient d dropped -- it never
# touches the slot), so the two machines agree on slots (go_state: the
# go-machine's remainder IS the structural twin's slot).  The visible
# countdown buys exactly the lemmas the ring correspondence needs:
#
#   go_state:   snd(go(n, m, d, r)) == snd(mm(n, m, r)).  The bridge, by
#               induction on n peeling m exactly as go does.
#   splice_go:  snd(mm(a+b, m, r)) ==
#               snd(mm(b, fst(mm(a, m, r)), snd(mm(a, m, r)))).
#               THE append lemma: running a+b ticks is running a, then
#               running b FROM THE STATE a left behind.  go cannot even
#               STATE this (its state is hidden); mm can, and the proof
#               is a plain induction on a -- every case is the IH itself.
#   slot_add:   the fence in STATE form: t <= m forces the slot to be
#               exactly r + t (no wrap can happen, the countdown outruns
#               the ticks).  This is mod_lt's fence re-cut for the
#               machine: the le_ok(t, m) witness peels one level per
#               tick, while lt_ok's add(t, 1n) shape would be stuck
#               under the successor.
#   lapg_cl/slg: one full lap (1+m ticks from countdown m) lands the
#               machine on the CANONICAL state: countdown r+m, slot 0.
#               mod_period is splice at the lap + this reset.
#   suminv:     states REACHED from a state with budget cp (the
#               countdown plus the slot) keep that budget -- the normal
#               tick trades one countdown for one slot (the same sum,
#               regrouped by add_succ), and the wrap hands the slot to
#               the countdown wholesale.  This is the bridge between
#               "t <= cp" (what mod_inj_lap knows) and "t <= m + r"
#               (what the machine injectivity needs at the reached
#               state).
#   mi_go:      THE machine injectivity: 1 <= t <= m+r forces the slot
#               after t ticks to differ from the current slot r.  A
#               TRICHOTOMY on (t, m), not an induction on t -- the
#               target slot would move with the state under tick
#               peeling, so instead:
#                 t <= m      no wrap: slot_add pins the slot to r+t,
#                             which differs from r (add_t_ne);
#                 t >= 1+m    one full lap lands on (r+m, 0) (the lap
#                             lemmas + splice at the lap) and the
#                             REMAINDER s = t-(1+m) charges the slot
#                             from 0 inside r's own countdown:
#                             slot_add pins it to s, and the budget
#                             bound gives 1+s <= r (mi_wrap_hb), so
#                             s != r (lt_ne_go).  The wrap is exactly
#                             where an under-capacity ring (bad_cap)
#                             would come back around to r itself --
#                             the budget is what forbids the extra lap.
#
# With these, the four laws are Equal.cong/trans plumbing:
#
#   mod_bound:       bridge, then the twin's slot never exceeds the
#                    state's budget (mbound_go), at the canonical state
#                    the budget is cp + 0.  Numpy gloss: i % cap < cap.
#   mod_period:      bridge, commute the lap to the front, splice at the
#                    lap, the lap reset.  Numpy gloss: (i+cap)%cap==i%cap.
#   mod_period_good: the pinned instance 9 % 4 == 5 % 4 == 1.
#   mod_inj_lap:     bridge both mods, splice at i, suminv + mi_go at
#                    the reached state.  Numpy gloss: two writes less
#                    than a lap apart never share a slot.
# --------------------------------------------------------------------------

# transport a True-fact across a Bool equality: {P == Q} with {Q == True}
# gives {P == True}.  (Equal.trans does all the work; this is the
# readability wrapper every bridge step below uses.)
def btrans(P: Bool, Q: Bool, e: {P == Q : Bool}, h: {Q == True{} : Bool})
  -> {P == True{} : Bool}:
  Equal.trans(Bool, P, Q, True{}, e, h)

# the twin: divmod.go's recursion with the countdown kept in the output.
def mm(n: Nat, m: Nat, r: Nat) -> Nat & Nat:
  match n:
    case 0n:
      (m, r)
    case 1n+np:
      match m:
        case 0n:
          mm(np, r, 0n)
        case 1n+mp:
          mm(np, mp, 1n+r)

# the bridge: the go-machine and the twin agree on the slot; the quotient
# d is irrelevant to it.  Induction on n, peeling m exactly as go does.
def go_state(n: Nat, m: Nat, d: Nat, r: Nat)
  -> {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r))
      == Pair.snd(Nat, Nat, mm(n, m, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          go_state(np, r, 1n+d, 0n)
        case 1n+mp:
          go_state(np, mp, d, 1n+r)

# the append lemma: a+b ticks from state (m, r) is b ticks from whatever
# state the first a ticks left.  Induction on a; both sides peel the same
# transition, so every case is the IH itself (the bases are definitional).
def splice_go(a: Nat, b: Nat, m: Nat, r: Nat)
  -> {Pair.snd(Nat, Nat, mm(Nat.add(a, b), m, r))
      == Pair.snd(Nat, Nat,
                  mm(b, Pair.fst(Nat, Nat, mm(a, m, r)),
                        Pair.snd(Nat, Nat, mm(a, m, r)))) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      match m:
        case 0n:
          splice_go(p, b, r, 0n)
        case 1n+mp:
          splice_go(p, b, mp, 1n+r)

# the slot never exceeds the state's whole budget, right-added form:
# r <= m + r.  The base is le_refl_b (m = 0), the step le_succ_of_le.
def slot_le_budget(+m: Nat, +r: Nat)
  -> {Nat.is_le(r, Nat.add(m, r)) == True{} : Bool}:
  match m:
    case 0n:
      Laws.le_refl_b(r)
    case 1n++p:
      Laws.le_succ_of_le(r, Nat.add(p, r), slot_le_budget(p, r))

# the twin's slot is bounded by the state's budget: slot <= m + r.
# Lockstep induction on n; the wrap case (m = 0) resets the budget to
# r + 0 (glued by add_zero), the normal step regroups it (add_succ).
def mbound_go(n: Nat, m: Nat, +r: Nat)
  -> {Nat.is_le(Pair.snd(Nat, Nat, mm(n, m, r)), Nat.add(m, r))
      == True{} : Bool}:
  match n:
    case 0n:
      slot_le_budget(m, r)
    case 1n++p:
      match m:
        case 0n:
          btrans(Nat.is_le(Pair.snd(Nat, Nat, mm(p, r, 0n)), r),
                 Nat.is_le(Pair.snd(Nat, Nat, mm(p, r, 0n)), Nat.add(r, 0n)),
                 Equal.cong(Nat, Bool,
                   x => Nat.is_le(Pair.snd(Nat, Nat, mm(p, r, 0n)), x),
                   r, Nat.add(r, 0n),
                   Equal.sym(Nat, Nat.add(r, 0n), r, Laws.add_zero(r))),
                 mbound_go(p, r, 0n))
        case 1n++mp:
          btrans(Nat.is_le(Pair.snd(Nat, Nat, mm(p, mp, 1n+r)),
                           1n+Nat.add(mp, r)),
                 Nat.is_le(Pair.snd(Nat, Nat, mm(p, mp, 1n+r)),
                           Nat.add(mp, 1n+r)),
                 Equal.cong(Nat, Bool,
                   x => Nat.is_le(Pair.snd(Nat, Nat, mm(p, mp, 1n+r)), x),
                   1n+Nat.add(mp, r), Nat.add(mp, 1n+r),
                   Equal.sym(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r),
                             Laws.add_succ(mp, r))),
                 mbound_go(p, mp, 1n+r))

# the fence in state form: t <= m forces the slot to be exactly r + t.
# The countdown consumes one per tick while the slot charges one, so
# below the fence no wrap can happen and the accumulation is linear.
# The le_ok witness peels one level per tick; t = 1+p at m = 0 is
# unsatisfiable and dies by the witness.
def slot_add(n: Nat, m: Nat, +r: Nat, h: R.le_ok(n, m))
  -> {Pair.snd(Nat, Nat, mm(n, m, r)) == Nat.add(r, n) : Nat}:
  match n m h:
    case 0n _ _:
      Equal.sym(Nat, Nat.add(r, 0n), r, Laws.add_zero(r))
    case 1n+p 0n h:
      Empty.absurd({Pair.snd(Nat, Nat, mm(1n+p, 0n, r))
                    == Nat.add(r, 1n+p) : Nat}, h)
    case 1n++p 1n++mp h:
      Equal.trans(Nat,
        Pair.snd(Nat, Nat, mm(p, mp, 1n+r)),
        Nat.add(1n+r, p),
        Nat.add(r, 1n+p),
        slot_add(p, mp, 1n+r, h),
        Equal.sym(Nat, Nat.add(r, 1n+p), Nat.add(1n+r, p),
                  Laws.add_succ(r, p)))

# one full lap, countdown half: 1+m ticks from (m, r) leave countdown
# r + m (the slot r charged m normal ticks, then became the countdown
# at the wrap).
def lapg_cl(+m: Nat, +r: Nat)
  -> {Pair.fst(Nat, Nat, mm(1n+m, m, r)) == Nat.add(r, m) : Nat}:
  match m:
    case 0n:
      Equal.sym(Nat, Nat.add(r, 0n), r, Laws.add_zero(r))
    case 1n++mp:
      Equal.trans(Nat,
        Pair.fst(Nat, Nat, mm(1n+mp, mp, 1n+r)),
        Nat.add(1n+r, mp),
        Nat.add(r, 1n+mp),
        lapg_cl(mp, 1n+r),
        Equal.sym(Nat, Nat.add(r, 1n+mp), Nat.add(1n+r, mp),
                  Laws.add_succ(r, mp)))

# one full lap, slot half: the slot resets to 0.  Induction on the
# countdown; the wrap is the last tick and hands the countdown to the
# twin's state.
def lapg_sl(m: Nat, r: Nat)
  -> {Pair.snd(Nat, Nat, mm(1n+m, m, r)) == 0n : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+mp:
      lapg_sl(mp, 1n+r)

# a < b implies a != b, in the decider shape the wrap case needs
# (le_ok(1+a, b) is the machine's own "one more tick than the fence").
def lt_ne_go(a: Nat, b: Nat, h: R.le_ok(Nat.add(1n, a), b))
  -> {Nat.is_ne(a, b) == True{} : Bool}:
  match a b h:
    case 0n 0n h:
      Empty.absurd({Nat.is_ne(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q h:
      {==}
    case 1n+p 0n h:
      Empty.absurd({Nat.is_ne(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q h:
      lt_ne_go(p, q, h)

# the fence weakened by one: 1+x <= r implies x <= r.  Needed because
# the wrap case's remaining ticks sit one below the fence.
def lemon1_go(x: Nat, r: Nat, +h: {Nat.is_le(1n+x, r) == True{} : Bool})
  -> {Nat.is_le(x, r) == True{} : Bool}:
  match x r h:
    case 0n 0n h:
      {==}
    case 0n 1n+rq h:
      {==}
    case 1n+q 0n h:
      Bool.fne({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+q 1n+rq h:
      lemon1_go(q, rq, h)

# r + t != r whenever 1 <= t: the slot charges past the target.  The
# t = 0 cases die on h1 (is_le(1, 0) is literally False); the succ step
# peels one successor on both sides.
def add_t_ne(r: Nat, t: Nat, h: {Nat.is_le(1n, t) == True{} : Bool})
  -> {Nat.is_ne(Nat.add(r, t), r) == True{} : Bool}:
  match r t h:
    case 0n 0n h:
      Bool.fne({Nat.is_ne(Nat.add(0n, 0n), 0n) == True{} : Bool}, h)
    case 0n 1n+q h:
      {==}
    case 1n+p 0n h:
      Bool.fne({Nat.is_ne(Nat.add(1n+p, 0n), 1n+p) == True{} : Bool}, h)
    case 1n+p 1n+q h:
      add_t_ne(p, 1n+q, h)

# cancellation on the shared left addend: m + x <= m + y implies x <= y.
# Peeling m peels the shared successor on both sides; m = 0 is the
# identity.  This converts the budget bound (t <= m + r) into the
# slot-vs-countdown comparison the wrap case needs.
def add_le_cancel(m: Nat, x: Nat, y: Nat,
                  h: {Nat.is_le(Nat.add(m, x), Nat.add(m, y))
                      == True{} : Bool})
  -> {Nat.is_le(x, y) == True{} : Bool}:
  match m h:
    case 0n h:
      h
    case 1n+p h:
      add_le_cancel(p, x, y, h)

# the reached-state invariant: from a state whose budget is cp (the
# countdown m plus the slot r), any number of ticks keeps the budget --
# the normal tick trades one countdown for one slot (the same sum,
# regrouped by add_succ), and the wrap hands the slot to the countdown
# wholesale.  This is what makes "t <= cp" mean "t <= m + r" at a
# reached state: the budget never left cp.
def suminv(i: Nat, m: Nat, +r: Nat, +cp: Nat,
           +h: {Nat.add(m, r) == cp : Nat})
  -> {Nat.add(Pair.fst(Nat, Nat, mm(i, m, r)),
              Pair.snd(Nat, Nat, mm(i, m, r))) == cp : Nat}:
  match i:
    case 0n:
      h
    case 1n+p:
      match m:
        case 0n:
          suminv(p, r, 0n, cp,
                 Equal.trans(Nat, Nat.add(r, 0n), r, cp,
                             Laws.add_zero(r), h))
        case 1n++mp:
          suminv(p, mp, 1n+r, cp,
                 Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), cp,
                             Laws.add_succ(mp, r), h))

# the trichotomy gadget: every pair of Nats splits into a <= b or
# a >= 1+b, as CONTINUATIONS carrying the decider witness (the le_ok
# Type form, which refines one successor per step).  Witness-passing
# avoids transporting proofs across Bool equalities entirely.
def nat_cases(a: Nat, b: Nat, -X: Type,
              kle: R.le_ok(a, b) -> X,
              kgt: R.le_ok(Nat.add(1n, b), a) -> X) -> X:
  match a b:
    case 0n _:
      kle(Unit{})
    case 1n+p 0n:
      kgt(Unit{})
    case 1n+p 1n+q:
      nat_cases(p, q, X, kle, kgt)

# the Bool-decider witness, extracted structurally: from a proof of
# is_le(a, b) == True one gets the le_ok(a, b) view (the unsatisfiable
# branches reduce the hypothesis to {False == True} and die by fne).
def b_le(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool})
  -> R.le_ok(a, b):
  match a b h:
    case 0n _ _:
      Unit{}
    case 1n+p 0n h:
      Bool.fne(R.le_ok(1n+p, 0n), h)
    case 1n+p 1n+q h:
      b_le(p, q, h)

# the no-wrap branch of the machine injectivity: t <= m, so slot_add
# pins the slot to r + t, and r + t differs from r because t >= 1.
def mi_kle(+t: Nat, +m: Nat, +r: Nat,
           h1: {Nat.is_le(1n, t) == True{} : Bool},
           wkle: R.le_ok(t, m))
  -> {Nat.is_ne(Pair.snd(Nat, Nat, mm(t, m, r)), r) == True{} : Bool}:
  btrans(Nat.is_ne(Pair.snd(Nat, Nat, mm(t, m, r)), r),
         Nat.is_ne(Nat.add(r, t), r),
         Equal.cong(Nat, Bool, x => Nat.is_ne(x, r),
                    Pair.snd(Nat, Nat, mm(t, m, r)), Nat.add(r, t),
                    slot_add(t, m, r, wkle)),
         add_t_ne(r, t, h1))

# the regrouping: m + (1+s) == t, where s = t - (1+m).  sub_add_cancel
# gives s + (1+m) == t; two associativity/commutativity steps move the
# m to the front: s + (1+m) -> 1 + (s+m) -> 1 + (m+s) == m + (1+s).
def t_to_ms(+t: Nat, +m: Nat,
            +h3: {Nat.is_le(Nat.add(1n, m), t) == True{} : Bool})
  -> {Nat.add(m, Nat.add(1n, Nat.sub(t, Nat.add(1n, m)))) == t : Nat}:
  Equal.trans(Nat,
    Nat.add(m, Nat.add(1n, Nat.sub(t, Nat.add(1n, m)))),
    1n+Nat.add(m, Nat.sub(t, Nat.add(1n, m))),
    t,
    Laws.add_succ(m, Nat.sub(t, Nat.add(1n, m))),
    Equal.trans(Nat,
      1n+Nat.add(m, Nat.sub(t, Nat.add(1n, m))),
      1n+Nat.add(Nat.sub(t, Nat.add(1n, m)), m),
      t,
      Equal.cong(Nat, Nat, x => 1n+x,
        Nat.add(m, Nat.sub(t, Nat.add(1n, m))),
        Nat.add(Nat.sub(t, Nat.add(1n, m)), m),
        Laws.add_comm(m, Nat.sub(t, Nat.add(1n, m)))),
      Equal.trans(Nat,
        1n+Nat.add(Nat.sub(t, Nat.add(1n, m)), m),
        Nat.add(Nat.sub(t, Nat.add(1n, m)), Nat.add(1n, m)),
        t,
        Equal.sym(Nat,
          Nat.add(Nat.sub(t, Nat.add(1n, m)), Nat.add(1n, m)),
          1n+Nat.add(Nat.sub(t, Nat.add(1n, m)), m),
          Laws.add_succ(Nat.sub(t, Nat.add(1n, m)), m)),
        Laws.sub_add_cancel(t, Nat.add(1n, m), h3))))

# the mirror regrouping: (1+m)+s == t.  t_to_ms gives m+(1+s) == t;
# both sides are 1+(m+s), so one add_succ on each side closes it.
def t_to_1ms(+t: Nat, +m: Nat,
             +h3: {Nat.is_le(Nat.add(1n, m), t) == True{} : Bool})
  -> {Nat.add(Nat.add(1n, m), Nat.sub(t, Nat.add(1n, m))) == t : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(1n, m), Nat.sub(t, Nat.add(1n, m))),
    Nat.add(Nat.sub(t, Nat.add(1n, m)), Nat.add(1n, m)),
    t,
    Laws.add_comm(Nat.add(1n, m), Nat.sub(t, Nat.add(1n, m))),
    Equal.trans(Nat,
      Nat.add(Nat.sub(t, Nat.add(1n, m)), Nat.add(1n, m)),
      Nat.add(m, Nat.add(1n, Nat.sub(t, Nat.add(1n, m)))),
      t,
      Equal.trans(Nat,
        Nat.add(Nat.sub(t, Nat.add(1n, m)), Nat.add(1n, m)),
        1n+Nat.add(m, Nat.sub(t, Nat.add(1n, m))),
        Nat.add(m, Nat.add(1n, Nat.sub(t, Nat.add(1n, m)))),
        Equal.trans(Nat,
          Nat.add(Nat.sub(t, Nat.add(1n, m)), Nat.add(1n, m)),
          1n+Nat.add(Nat.sub(t, Nat.add(1n, m)), m),
          1n+Nat.add(m, Nat.sub(t, Nat.add(1n, m))),
          Laws.add_succ(Nat.sub(t, Nat.add(1n, m)), m),
          Equal.cong(Nat, Nat,
            z => 1n+z,
            Nat.add(Nat.sub(t, Nat.add(1n, m)), m),
            Nat.add(m, Nat.sub(t, Nat.add(1n, m))),
            Laws.add_comm(Nat.sub(t, Nat.add(1n, m)), m))),
        Equal.sym(Nat,
          Nat.add(m, Nat.add(1n, Nat.sub(t, Nat.add(1n, m)))),
          1n+Nat.add(m, Nat.sub(t, Nat.add(1n, m))),
          Laws.add_succ(m, Nat.sub(t, Nat.add(1n, m))))),
      t_to_ms(t, m, h3)))

# the wrap branch's arithmetic core: from t >= 1+m and the budget bound
# t <= m + r, the remainder s = t - (1+m) satisfies 1+s <= r.  Proof:
# sub_add_cancel turns m + (1+s) back into t (the subtraction cancels),
# so after cancelling the shared m the goal IS the budget bound h2.
def mi_wrap_hb(+t: Nat, +m: Nat, +r: Nat,
               +h2: {Nat.is_le(t, Nat.add(m, r)) == True{} : Bool},
               +h3: {Nat.is_le(Nat.add(1n, m), t) == True{} : Bool})
  -> {Nat.is_le(Nat.add(1n, Nat.sub(t, Nat.add(1n, m))), r)
      == True{} : Bool}:
  add_le_cancel(m, Nat.add(1n, Nat.sub(t, Nat.add(1n, m))), r,
    btrans(Nat.is_le(Nat.add(m, Nat.add(1n, Nat.sub(t, Nat.add(1n, m)))),
                     Nat.add(m, r)),
           Nat.is_le(t, Nat.add(m, r)),
           Equal.cong(Nat, Bool, x => Nat.is_le(x, Nat.add(m, r)),
             Nat.add(m, Nat.add(1n, Nat.sub(t, Nat.add(1n, m)))), t,
             Equal.sym(Nat, t,
               Nat.add(m, Nat.add(1n, Nat.sub(t, Nat.add(1n, m)))),
               Equal.sym(Nat,
                 Nat.add(m, Nat.add(1n, Nat.sub(t, Nat.add(1n, m)))),
                 t,
                 t_to_ms(t, m, h3)))),
           h2))

# the wrap branch: t >= 1+m.  Step 1: rewrite t as (1+m)+s (with
# s = t-(1+m), by sub_add_cancel).  Step 2: splice the lap off, leaving
# s ticks from the lap's landing state.  Step 3: the lap lemmas rewrite
# the landing state's SLOT to 0 (lapg_sl) and its COUNTDOWN to r+m
# (lapg_cl) -- the state is (r+m, 0), the canonical shape again.  Step
# 4: slot_add pins the slot after s ticks from (r+m, 0) to 0+s
# (add_zero), i.e. exactly s; mi_wrap_hb's 1+s <= r makes s != r
# (lt_ne_go).  An under-capacity ring violates exactly here: with room
# for one more lap the slot would come back around to r itself.
def mi_wrap(+t: Nat, +m: Nat, +r: Nat,
            +h2: {Nat.is_le(t, Nat.add(m, r)) == True{} : Bool},
            +h3: {Nat.is_le(Nat.add(1n, m), t) == True{} : Bool})
  -> {Nat.is_ne(Pair.snd(Nat, Nat, mm(t, m, r)), r) == True{} : Bool}:
  btrans(Nat.is_ne(Pair.snd(Nat, Nat, mm(t, m, r)), r),
    Nat.is_ne(Pair.snd(Nat, Nat,
      mm(Nat.add(1n+m, Nat.sub(t, Nat.add(1n, m))), m, r)), r),
    Equal.cong(Nat, Bool,
      x => Nat.is_ne(Pair.snd(Nat, Nat, mm(x, m, r)), r),
      t,
      Nat.add(1n+m, Nat.sub(t, Nat.add(1n, m))),
      Equal.sym(Nat, Nat.add(1n+m, Nat.sub(t, Nat.add(1n, m))), t,
        t_to_1ms(t, m, h3))),
    btrans(Nat.is_ne(Pair.snd(Nat, Nat,
             mm(Nat.add(1n+m, Nat.sub(t, Nat.add(1n, m))), m, r)), r),
      Nat.is_ne(Pair.snd(Nat, Nat,
        mm(Nat.sub(t, Nat.add(1n, m)),
           Pair.fst(Nat, Nat, mm(1n+m, m, r)),
           Pair.snd(Nat, Nat, mm(1n+m, m, r)))), r),
      Equal.cong(Nat, Bool,
        x => Nat.is_ne(x, r),
        Pair.snd(Nat, Nat,
          mm(Nat.add(1n+m, Nat.sub(t, Nat.add(1n, m))), m, r)),
        Pair.snd(Nat, Nat,
          mm(Nat.sub(t, Nat.add(1n, m)),
             Pair.fst(Nat, Nat, mm(1n+m, m, r)),
             Pair.snd(Nat, Nat, mm(1n+m, m, r)))),
        splice_go(1n+m, Nat.sub(t, Nat.add(1n, m)), m, r)),
      btrans(Nat.is_ne(Pair.snd(Nat, Nat,
               mm(Nat.sub(t, Nat.add(1n, m)),
                  Pair.fst(Nat, Nat, mm(1n+m, m, r)),
                  Pair.snd(Nat, Nat, mm(1n+m, m, r)))), r),
        Nat.is_ne(Pair.snd(Nat, Nat,
          mm(Nat.sub(t, Nat.add(1n, m)),
             Pair.fst(Nat, Nat, mm(1n+m, m, r)), 0n)), r),
        Equal.cong(Nat, Bool,
          x => Nat.is_ne(Pair.snd(Nat, Nat,
            mm(Nat.sub(t, Nat.add(1n, m)),
               Pair.fst(Nat, Nat, mm(1n+m, m, r)), x)), r),
          Pair.snd(Nat, Nat, mm(1n+m, m, r)), 0n,
          lapg_sl(m, r)),
        btrans(Nat.is_ne(Pair.snd(Nat, Nat,
                 mm(Nat.sub(t, Nat.add(1n, m)),
                    Pair.fst(Nat, Nat, mm(1n+m, m, r)), 0n)), r),
          Nat.is_ne(Pair.snd(Nat, Nat,
            mm(Nat.sub(t, Nat.add(1n, m)), Nat.add(r, m), 0n)), r),
          Equal.cong(Nat, Bool,
            x => Nat.is_ne(Pair.snd(Nat, Nat,
              mm(Nat.sub(t, Nat.add(1n, m)), x, 0n)), r),
            Pair.fst(Nat, Nat, mm(1n+m, m, r)), Nat.add(r, m),
            lapg_cl(m, r)),
          btrans(Nat.is_ne(Pair.snd(Nat, Nat,
                   mm(Nat.sub(t, Nat.add(1n, m)), Nat.add(r, m), 0n)), r),
            Nat.is_ne(Nat.add(0n, Nat.sub(t, Nat.add(1n, m))), r),
            Equal.cong(Nat, Bool,
              x => Nat.is_ne(x, r),
              Pair.snd(Nat, Nat,
                mm(Nat.sub(t, Nat.add(1n, m)), Nat.add(r, m), 0n)),
              Nat.add(0n, Nat.sub(t, Nat.add(1n, m))),
              slot_add(Nat.sub(t, Nat.add(1n, m)), Nat.add(r, m), 0n,
                b_le(Nat.sub(t, Nat.add(1n, m)), Nat.add(r, m),
                  btrans(Nat.is_le(Nat.sub(t, Nat.add(1n, m)), Nat.add(r, m)),
                    Nat.is_le(Nat.sub(t, Nat.add(1n, m)), Nat.add(m, r)),
                    Equal.cong(Nat, Bool,
                      x => Nat.is_le(Nat.sub(t, Nat.add(1n, m)), x),
                      Nat.add(r, m), Nat.add(m, r),
                      Laws.add_comm(r, m)),
                    Laws.le_trans(Nat.sub(t, Nat.add(1n, m)), r, Nat.add(m, r),
                      lemon1_go(Nat.sub(t, Nat.add(1n, m)), r,
                        mi_wrap_hb(t, m, r, h2, h3)),
                      slot_le_budget(m, r)))))),
            btrans(Nat.is_ne(Nat.add(0n, Nat.sub(t, Nat.add(1n, m))), r),
              Nat.is_ne(Nat.sub(t, Nat.add(1n, m)), r),
              Equal.cong(Nat, Bool, x => Nat.is_ne(x, r),
                Nat.add(0n, Nat.sub(t, Nat.add(1n, m))),
                Nat.sub(t, Nat.add(1n, m)),
                {==}),
              lt_ne_go(Nat.sub(t, Nat.add(1n, m)), r,
                b_le(Nat.add(1n, Nat.sub(t, Nat.add(1n, m))), r,
                  mi_wrap_hb(t, m, r, h2, h3)))))))))

# THE machine injectivity: 1 <= t <= m+r forces the slot after t ticks
# to differ from the current slot r.  The trichotomy (not an induction
# on t -- the target would move under tick peeling):
#   t <= m   the fence holds, no wrap (mi_kle);
#   t >= 1+m one lap plus a remainder strictly inside r (mi_wrap).
def mi_go(+t: Nat, +m: Nat, +r: Nat,
          +h1: {Nat.is_le(1n, t) == True{} : Bool},
          +h2: {Nat.is_le(t, Nat.add(m, r)) == True{} : Bool})
  -> {Nat.is_ne(Pair.snd(Nat, Nat, mm(t, m, r)), r) == True{} : Bool}:
  nat_cases(t, m,
    {Nat.is_ne(Pair.snd(Nat, Nat, mm(t, m, r)), r) == True{} : Bool},
    wkle => mi_kle(t, m, r, h1, wkle),
    wkgt => mi_wrap(t, m, r, h2, Laws.le_ok_iff(Nat.add(1n, m), t, wkgt)))

# mod_bound: the slot is inside the ring.  The go-machine's slot is the
# twin's (go_state); the twin's slot never exceeds the state's budget
# (mbound_go); at the canonical state (cp, 0) the budget is cp + 0.
# The numpy gloss: i % cap is a valid index into a cap-length buffer.
def Laws.mod_bound(n, cp):
  Equal.trans(Bool,
    Nat.is_le(Pair.snd(Nat, Nat, Nat.divmod.go(n, cp, 0n, 0n)), cp),
    Nat.is_le(Pair.snd(Nat, Nat, mm(n, cp, 0n)), cp),
    True{},
    Equal.cong(Nat, Bool, x => Nat.is_le(x, cp),
      Pair.snd(Nat, Nat, Nat.divmod.go(n, cp, 0n, 0n)),
      Pair.snd(Nat, Nat, mm(n, cp, 0n)),
      go_state(n, cp, 0n, 0n)),
    btrans(Nat.is_le(Pair.snd(Nat, Nat, mm(n, cp, 0n)), cp),
           Nat.is_le(Pair.snd(Nat, Nat, mm(n, cp, 0n)), Nat.add(cp, 0n)),
           Equal.cong(Nat, Bool,
             x => Nat.is_le(Pair.snd(Nat, Nat, mm(n, cp, 0n)), x),
             cp, Nat.add(cp, 0n),
             Equal.sym(Nat, Nat.add(cp, 0n), cp, Laws.add_zero(cp))),
           mbound_go(n, cp, 0n)))

# mod_period: one lap later the slot address repeats.  Bridge both mods
# to the twin; commute the lap to the front (add_comm); splice at the
# lap (1+cp ticks from (cp, 0) is n ticks from the lap's landing
# state); the lap lemmas say that landing state IS (cp, 0) again --
# countdown 0+cp (lapg_cl), slot 0 (lapg_sl).  The numpy gloss:
# (i + cap) % cap == i % cap -- the ring's whole point.
def Laws.mod_period(n, cp):
  Equal.trans(Nat,
    Nat.mod(Nat.add(n, 1n+cp), 1n+cp),
    Pair.snd(Nat, Nat, mm(Nat.add(n, 1n+cp), cp, 0n)),
    Nat.mod(n, 1n+cp),
    go_state(Nat.add(n, 1n+cp), cp, 0n, 0n),
    Equal.trans(Nat,
      Pair.snd(Nat, Nat, mm(Nat.add(n, 1n+cp), cp, 0n)),
      Pair.snd(Nat, Nat, mm(n, cp, 0n)),
      Pair.snd(Nat, Nat, Nat.divmod.go(n, cp, 0n, 0n)),
      Equal.trans(Nat,
        Pair.snd(Nat, Nat, mm(Nat.add(n, 1n+cp), cp, 0n)),
        Pair.snd(Nat, Nat, mm(Nat.add(1n+cp, n), cp, 0n)),
        Pair.snd(Nat, Nat, mm(n, cp, 0n)),
        Equal.cong(Nat, Nat, x => Pair.snd(Nat, Nat, mm(x, cp, 0n)),
          Nat.add(n, 1n+cp), Nat.add(1n+cp, n),
          Equal.trans(Nat, Nat.add(n, 1n+cp), 1n+Nat.add(n, cp), Nat.add(1n+cp, n),
            Laws.add_succ(n, cp),
            Equal.cong(Nat, Nat, z => 1n+z, Nat.add(n, cp), Nat.add(cp, n),
              Laws.add_comm(n, cp)))),
        Equal.trans(Nat,
          Pair.snd(Nat, Nat, mm(Nat.add(1n+cp, n), cp, 0n)),
          Pair.snd(Nat, Nat,
            mm(n, Pair.fst(Nat, Nat, mm(1n+cp, cp, 0n)),
                  Pair.snd(Nat, Nat, mm(1n+cp, cp, 0n)))),
          Pair.snd(Nat, Nat, mm(n, cp, 0n)),
          splice_go(1n+cp, n, cp, 0n),
          Equal.trans(Nat,
            Pair.snd(Nat, Nat,
              mm(n, Pair.fst(Nat, Nat, mm(1n+cp, cp, 0n)),
                    Pair.snd(Nat, Nat, mm(1n+cp, cp, 0n)))),
            Pair.snd(Nat, Nat,
              mm(n, Pair.fst(Nat, Nat, mm(1n+cp, cp, 0n)), 0n)),
            Pair.snd(Nat, Nat, mm(n, cp, 0n)),
            Equal.cong(Nat, Nat,
              x => Pair.snd(Nat, Nat, mm(n, Pair.fst(Nat, Nat, mm(1n+cp, cp, 0n)), x)),
              Pair.snd(Nat, Nat, mm(1n+cp, cp, 0n)), 0n,
              lapg_sl(cp, 0n)),
            Equal.cong(Nat, Nat,
              x => Pair.snd(Nat, Nat, mm(n, x, 0n)),
              Pair.fst(Nat, Nat, mm(1n+cp, cp, 0n)), Nat.add(0n, cp),
              lapg_cl(cp, 0n))))),
      Equal.sym(Nat,
        Pair.snd(Nat, Nat, Nat.divmod.go(n, cp, 0n, 0n)),
        Pair.snd(Nat, Nat, mm(n, cp, 0n)),
        go_state(n, cp, 0n, 0n))))

# the pinned instance: 9 % 4 == 5 % 4 == 1, one lap apart.
def Laws.mod_period_good():
  Laws.mod_period(5n, 3n)

# mod_inj_lap: THE no-clobber law.  Bridge both mods to the twin;
# splice at i -- so the write at i+t is t ticks from the state i left
# behind, (cl_i, sl_i); the reached-state invariant (suminv) says that
# state's budget is still cp, which is exactly the fence mi_go needs to
# keep t inside one lap of it.  mi_go closes: the slot at i+t differs
# from the slot at i.  The numpy gloss: two writes less than a lap
# apart never share a slot.
def Laws.mod_inj_lap(i, t, cp, h1, h2):
  Equal.trans(Bool,
    Nat.is_ne(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(i, t), cp, 0n, 0n)),
              Pair.snd(Nat, Nat, Nat.divmod.go(i, cp, 0n, 0n))),
    Nat.is_ne(Pair.snd(Nat, Nat,
                        mm(t, Pair.fst(Nat, Nat, mm(i, cp, 0n)),
                              Pair.snd(Nat, Nat, mm(i, cp, 0n)))),
              Pair.snd(Nat, Nat, Nat.divmod.go(i, cp, 0n, 0n))),
    True{},
    Equal.cong(Nat, Bool,
      x => Nat.is_ne(x, Pair.snd(Nat, Nat, Nat.divmod.go(i, cp, 0n, 0n))),
      Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(i, t), cp, 0n, 0n)),
      Pair.snd(Nat, Nat,
        mm(t, Pair.fst(Nat, Nat, mm(i, cp, 0n)),
              Pair.snd(Nat, Nat, mm(i, cp, 0n)))),
      Equal.trans(Nat,
        Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(i, t), cp, 0n, 0n)),
        Pair.snd(Nat, Nat, mm(Nat.add(i, t), cp, 0n)),
        Pair.snd(Nat, Nat,
          mm(t, Pair.fst(Nat, Nat, mm(i, cp, 0n)),
                Pair.snd(Nat, Nat, mm(i, cp, 0n)))),
        go_state(Nat.add(i, t), cp, 0n, 0n),
        splice_go(i, t, cp, 0n))),
    Equal.trans(Bool,
      Nat.is_ne(Pair.snd(Nat, Nat,
                        mm(t, Pair.fst(Nat, Nat, mm(i, cp, 0n)),
                              Pair.snd(Nat, Nat, mm(i, cp, 0n)))),
              Pair.snd(Nat, Nat, Nat.divmod.go(i, cp, 0n, 0n))),
      Nat.is_ne(Pair.snd(Nat, Nat,
                        mm(t, Pair.fst(Nat, Nat, mm(i, cp, 0n)),
                              Pair.snd(Nat, Nat, mm(i, cp, 0n)))),
              Pair.snd(Nat, Nat, mm(i, cp, 0n))),
      True{},
      Equal.cong(Nat, Bool,
        x => Nat.is_ne(Pair.snd(Nat, Nat,
                          mm(t, Pair.fst(Nat, Nat, mm(i, cp, 0n)),
                                Pair.snd(Nat, Nat, mm(i, cp, 0n)))), x),
        Pair.snd(Nat, Nat, Nat.divmod.go(i, cp, 0n, 0n)),
        Pair.snd(Nat, Nat, mm(i, cp, 0n)),
        go_state(i, cp, 0n, 0n)),
      mi_go(t, Pair.fst(Nat, Nat, mm(i, cp, 0n)),
               Pair.snd(Nat, Nat, mm(i, cp, 0n)), h1,
        btrans(Nat.is_le(t, Nat.add(Pair.fst(Nat, Nat, mm(i, cp, 0n)),
                                    Pair.snd(Nat, Nat, mm(i, cp, 0n)))),
               Nat.is_le(t, cp),
               Equal.cong(Nat, Bool, x => Nat.is_le(t, x),
                 Nat.add(Pair.fst(Nat, Nat, mm(i, cp, 0n)),
                         Pair.snd(Nat, Nat, mm(i, cp, 0n))), cp,
                 suminv(i, cp, 0n, cp, Laws.add_zero(cp))),
               h2))))

# --------------------------------------------------------------------------
# 6f. the ring write path: hist_len_snoc, ring_write_snoc, ring_write_read,
#     ring_write_stable, ring_snoc_stable, ring_of_first_lap, the instances
# --------------------------------------------------------------------------
# The write laws of section 6f, in dependency order: the two bricks first
# (the tape's length twin, the extension write), then the slot laws (an
# induction on the list with the witness refining), then the tick form
# (pure composition: mod_inj_lap + the slot form + the length chain),
# then the fold (a go-lemma with an accumulator invariant, two small
# Bool-form sum converters so the fence witness stays reusable, and an
# append helper), then the pinned instances by normalisation.

# hist_len_snoc: the tape grows by exactly one.  Both sides peel one
# successor per cons; the cons case is the IH under a successor.
def hist_len_snoc_go(+xs: List<&2, F32>, +v: F32)
  -> {H.hist_len(H.hist_snoc(xs, v)) == 1n+H.hist_len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %hist_len_snoc_go(t, v)
        : {1n+H.hist_len(H.hist_snoc(t, v)) == 1n+_ : Nat}
      {==}

def Laws.hist_len_snoc(xs, v):
  hist_len_snoc_go(xs, v)

# ring_write_snoc: the extension write is the append.  The Nil case is
# definitional (both sides are the singleton); the cons case peels one
# successor on both sides -- the slot steps into the tail while the snoc
# rebuilds the head.
def ring_write_snoc_go(+xs: List<&2, F32>, +v: F32)
  -> {H.ring_write(xs, v, H.hist_len(xs)) == H.hist_snoc(xs, v)
      : List<&2, F32>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %ring_write_snoc_go(t, v)
        : {h <> H.ring_write(t, v, H.hist_len(t)) == h <> _ : List<&2, F32>}
      {==}

def Laws.ring_write_snoc(xs, v):
  ring_write_snoc_go(xs, v)

# 1n+p <= 0 is Empty once p is destructed (either shape of p reduces the
# le_ok match) -- the Nil-tape absurdity the write laws' witnesses need.
def le_succ_zero_absurd(p: Nat, h: R.le_ok(1n+p, 0n)) -> Empty:
  match p h:
    case 0n h:
      h
    case 1n+q h:
      h

# ring_write_read: induction on xs, the witness refining with the slot.
# Nil forces s = 0n (le_ok(1+p, 0) is Empty); s = 0 is the definitional
# overwrite; s = 1+p descends into the tail with the refined witness.
def ring_write_read_go(+xs: List<&2, F32>, +v: F32, +ic: F32, s: Nat,
                       h: R.le_ok(s, H.hist_len(xs)))
  -> {H.hist_read(H.ring_write(xs, v, s), s, ic) == v : F32}:
  match xs s h:
    case Nil{} 0n _:
      {==}
    case Nil{} 1n+p h:
      Empty.absurd({H.hist_read(H.ring_write(Nil{}, v, 1n+p), 1n+p, ic)
                    == v : F32},
                   le_succ_zero_absurd(p, h))
    case h <> t 0n _:
      {==}
    case h <> t 1n+p h:
      ring_write_read_go(t, v, ic, p, h)

def Laws.ring_write_read(xs, v, ic, s, h):
  ring_write_read_go(xs, v, ic, s, h)

# ring_write_stable: induction on xs, peeling (i, w) in lockstep so the
# disequality decider refines with them.  i = w is refuted by the decider
# (is_ne computes False on equal heads); a write at w = 0 keeps the head
# (reads below never see it); a write at w >= 1 keeps every head it
# passes -- the recursion.  No bound on i is needed: past the end both
# sides answer the IC fill, so only the write's slot needs the witness.
def ring_write_stable_go(+xs: List<&2, F32>, +v: F32, +ic: F32,
                         i: Nat, w: Nat,
                         hne: {Nat.is_ne(i, w) == True{} : Bool},
                         hw: R.le_ok(w, H.hist_len(xs)))
  -> {H.hist_read(H.ring_write(xs, v, w), i, ic)
      == H.hist_read(xs, i, ic) : F32}:
  match xs i w hne hw:
    case Nil{} 0n 0n hne _:
      Bool.fne({H.hist_read(H.ring_write(Nil{}, v, 0n), 0n, ic)
                == H.hist_read(Nil{}, 0n, ic) : F32}, hne)
    case Nil{} 1n+p 0n hne _:
      {==}
    case Nil{} _ 1n+q hne hw:
      Empty.absurd({H.hist_read(H.ring_write(Nil{}, v, 1n+q), i, ic)
                    == H.hist_read(Nil{}, i, ic) : F32},
                   le_succ_zero_absurd(q, hw))
    case h <> t 0n 0n hne _:
      Bool.fne({H.hist_read(H.ring_write(h <> t, v, 0n), 0n, ic)
                == H.hist_read(h <> t, 0n, ic) : F32}, hne)
    case h <> t 0n 1n+q hne _:
      {==}
    case h <> t 1n+p 0n hne _:
      {==}
    case h <> t 1n+p 1n+q hne hw:
      ring_write_stable_go(t, v, ic, p, q, hne, hw)

def Laws.ring_write_stable(xs, v, ic, i, w, hne, hw):
  ring_write_stable_go(xs, v, ic, i, w, hne, hw)

# ring_snoc_stable: pure composition.  ring_read/ring_snoc unfold to the
# slot forms definitionally, so the goal IS the slot-form stability at
# slots mod(i, cap) vs mod(i+t, cap); mod_inj_lap supplies the
# disequality decider, and the length chain (mod_bound, the full-ring
# witness weakened by one, le_trans, b_le) supplies the write's bounds
# witness.
def Laws.ring_snoc_stable(ring, v, ic, i, t, cp, hfull, h1, h2):
  Laws.ring_write_stable(ring, v, ic, Nat.mod(i, 1n+cp),
    Nat.mod(Nat.add(i, t), 1n+cp),
    ne_symm(Nat.mod(Nat.add(i, t), 1n+cp), Nat.mod(i, 1n+cp),
      Laws.mod_inj_lap(i, t, cp, h1, h2)),
    b_le(Nat.mod(Nat.add(i, t), 1n+cp), H.hist_len(ring),
      Laws.le_trans(Nat.mod(Nat.add(i, t), 1n+cp), cp, H.hist_len(ring),
        Laws.mod_bound(Nat.add(i, t), cp),
        lemon1_go(cp, H.hist_len(ring),
          Laws.le_ok_iff(1n+cp, H.hist_len(ring), hfull)))))

# ---- the fold's helpers: an append, its snoc-move, the sum converters ----

# the append, recursing on the FIRST argument (the go-lemma's RHS shape):
# happ2(acc, b) is acc ++ b.  Proof-internal: the law statement stays
# clean (ring_of == xs), the helper never leaves this section.
def happ2(+acc: List<&2, F32>, +b: List<&2, F32>) -> List<&2, F32>:
  match acc:
    case Nil{}:
      b
    case h <> t:
      h <> happ2(t, b)

# append's nil-right half: happ2(acc, Nil) == acc -- the go-lemma's base
# case.  Induction on acc, the IH under the head.
def happ2_nil_r(+acc: List<&2, F32>)
  -> {happ2(acc, Nil{}) == acc : List<&2, F32>}:
  match acc:
    case Nil{}:
      {==}
    case h <> t:
      %happ2_nil_r(t)
        : {h <> happ2(t, Nil{}) == h <> _ : List<&2, F32>}
      {==}

# append's snoc-move: happ2(snoc(acc, h), t) == happ2(acc, h <> t) -- the
# append's defining equation, the bridge the fold's step case needs.
# Induction on acc: both sides rebuild the same head.
def happ2_snoc_move(+acc: List<&2, F32>, +h: F32, +t: List<&2, F32>)
  -> {happ2(H.hist_snoc(acc, h), t) == happ2(acc, h <> t)
      : List<&2, F32>}:
  match acc:
    case Nil{}:
      {==}
    case a <> t2:
      %happ2_snoc_move(t2, h, t)
        : {a <> happ2(H.hist_snoc(t2, h), t) == a <> _ : List<&2, F32>}
      {==}

# the sum-shift, Bool form: tick + (1+len) <= cap implies (1+tick) + len
# <= cap -- the step moves the successor from the tape side of the sum to
# the tick side.  Induction peeling tick and cap in lockstep; the
# Bool-typed hypothesis is + (Data), so ONE witness serves both the fence
# and the recursion.
def sum_le_shift_go(tick: Nat, +b: Nat, +c: Nat,
                    +h: {Nat.is_le(Nat.add(tick, 1n+b), c) == True{} : Bool})
  -> {Nat.is_le(Nat.add(1n+tick, b), c) == True{} : Bool}:
  match tick c h:
    case 0n 0n h:
      Bool.fne({Nat.is_le(Nat.add(1n, b), 0n) == True{} : Bool}, h)
    case 0n 1n+cp h:
      h
    case 1n+q 0n h:
      Bool.fne({Nat.is_le(Nat.add(1n+1n+q, b), 0n) == True{} : Bool}, h)
    case 1n+q 1n+cp h:
      sum_le_shift_go(q, b, cp, h)

# the fence from the sum, Bool form: tick + (1+len) <= cap implies
# tick < cap -- the +1 on the tape side is what keeps the fence strict.
# The successor cases of lt_ok peel with the induction.
def lt_of_sum_le_go(tick: Nat, +b: Nat, +c: Nat,
                    +h: {Nat.is_le(Nat.add(tick, 1n+b), c) == True{} : Bool})
  -> R.lt_ok(tick, c):
  match tick c h:
    case 0n 0n h:
      Bool.fne(R.lt_ok(0n, 0n), h)
    case 0n 1n+cp h:
      Unit{}
    case 1n+q 0n h:
      Bool.fne(R.lt_ok(1n+q, 0n), h)
    case 1n+q 1n+cp h:
      lt_of_sum_le_go(q, b, cp, h)

# hist_len(Nil) is 0: the top-level accumulator's length witness.
def hist_len_nil() -> {H.hist_len(Nil{}) == 0n : Nat}:
  {==}

# THE go-lemma: the first-lap fold is the append.  Invariant: the
# accumulator IS the first `tick` ticks (hlen), and every remaining tick
# is below the fence (hfit: tick + len <= cap, so the CURRENT tick is
# strictly inside -- lt_of_sum_le_go).  Then the write at slot
# mod(tick, cap) = tick (mod_lt) = len(acc) (hlen) is an extension,
# i.e. a snoc (ring_write_snoc); the accumulator's length invariant is
# rebuilt by hist_len_snoc, the fence invariant by sum_le_shift_go, and
# the RHS by happ2_snoc_move.  All the bridging is Equal plumbing.
def ring_of_first_go(+xs: List<&2, F32>, +cap: Nat, +tick: Nat,
                     +acc: List<&2, F32>,
                     +hlen: {H.hist_len(acc) == tick : Nat},
                     +hfit: {Nat.is_le(Nat.add(tick, H.hist_len(xs)), cap)
                             == True{} : Bool})
  -> {H.ring_of_go(xs, cap, tick, acc) == happ2(acc, xs) : List<&2, F32>}:
  match xs:
    case Nil{}:
      Equal.sym(List<&2, F32>, happ2(acc, Nil{}), acc, happ2_nil_r(acc))
    case h <> t:
      Equal.trans(List<&2, F32>,
        H.ring_of_go(t, cap, 1n+tick, H.ring_write(acc, h, Nat.mod(tick, cap))),
        H.ring_of_go(t, cap, 1n+tick, H.hist_snoc(acc, h)),
        happ2(acc, h <> t),
        Equal.cong(List<&2, F32>, List<&2, F32>,
          z => H.ring_of_go(t, cap, 1n+tick, z),
          H.ring_write(acc, h, Nat.mod(tick, cap)),
          H.hist_snoc(acc, h),
          Equal.trans(List<&2, F32>,
            H.ring_write(acc, h, Nat.mod(tick, cap)),
            H.ring_write(acc, h, H.hist_len(acc)),
            H.hist_snoc(acc, h),
            Equal.cong(Nat, List<&2, F32>, s => H.ring_write(acc, h, s),
              Nat.mod(tick, cap), H.hist_len(acc),
              Equal.trans(Nat, Nat.mod(tick, cap), tick, H.hist_len(acc),
                Laws.mod_lt(tick, cap, lt_of_sum_le_go(tick, H.hist_len(t), cap, hfit)),
                Equal.sym(Nat, H.hist_len(acc), tick, hlen))),
            Laws.ring_write_snoc(acc, h))),
        Equal.trans(List<&2, F32>,
          H.ring_of_go(t, cap, 1n+tick, H.hist_snoc(acc, h)),
          happ2(H.hist_snoc(acc, h), t),
          happ2(acc, h <> t),
          ring_of_first_go(t, cap, 1n+tick, H.hist_snoc(acc, h),
            Equal.trans(Nat, H.hist_len(H.hist_snoc(acc, h)),
              1n+H.hist_len(acc), 1n+tick,
              Laws.hist_len_snoc(acc, h),
              Equal.cong(Nat, Nat, z => 1n+z, H.hist_len(acc), tick, hlen)),
            sum_le_shift_go(tick, H.hist_len(t), cap, hfit)),
          happ2_snoc_move(acc, h, t)))

# ring_of_first_lap: the top call.  The accumulator is Nil at tick 0
# (hist_len_nil), the fence is the law's own witness (le_ok_iff puts it
# in the sum's Bool form), and the go-lemma's RHS happ2(Nil, xs) is xs
# definitionally -- the fold IS the tape.
def Laws.ring_of_first_lap(xs, cap, h):
  ring_of_first_go(xs, cap, 0n, Nil{}, hist_len_nil(),
    Laws.le_ok_iff(H.hist_len(xs), cap, h))

# the pinned instances: pure computation, definitional (mod on literals,
# ring_write on literal lists, the samples carried structurally).
def Laws.ring_of_good_4():
  {==}

def Laws.ring_read_live_good_4():
  {==}

def Laws.ring_read_stale_good_4():
  {==}

# --------------------------------------------------------------------------
# 8. THE CONTRACT: the three capstones and their lemma ladders
# --------------------------------------------------------------------------

# ---- ingress_contract (adapted from PROOF_json.bend's json_read_fresh) ----

# and-introduction, the mirror of the and_elim pair (filled laws do not
# re-export across module imports, so it is restated here)
def and_intro(a: Bool, b: Bool,
              +ha: {a == True{} : Bool},
              +hb: {b == True{} : Bool})
    -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      Bool.fne({Bool.and(False{}, b) == True{} : Bool}, ha)

# the leaf: one bumped line is fresh.  route_bump reads at delay
# 1 + newest + e, so route_read's d>=1 branch gives i1 = sub(n, n+e) and
# freshness is sub_le_b (n - anything <= n) at the lane's newest n.
def bump_fresh(+ls: List<&2, R.Lane>, +p: R.Proj, +e: Nat)
    -> {J.line_fresh(ls, J.route_bump(ls, p, e), R.proj_src(p)) == True{} : Bool}:
  Laws.sub_le_b(R.lane_newest(R.nth_lane(ls, R.proj_src(p))),
                Nat.add(R.lane_newest(R.nth_lane(ls, R.proj_src(p))), e))

# the fold: pointwise freshness over the projection list, mirroring the
# runtime predicate's own recursion
def bumps_fresh_go(+ls: List<&2, R.Lane>, ps: List<&2, R.Proj>, +e: Nat)
    -> {J.bumps_fresh(ls, ps, e) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +h <> +t:
      and_intro(J.line_fresh(ls, J.route_bump(ls, h, e), R.proj_src(h)),
               J.bumps_fresh(ls, t, e),
               bump_fresh(ls, h, e),
               bumps_fresh_go(ls, t, e))

def Laws.ingress_contract(s, m, h):
  bumps_fresh_go(J.lanes_run(m, R.init_lanes(R.cfg_lanes(J.json_decode(s)))),
                 R.cfg_projs(J.json_decode(s)), 0n)

# ---- routing_contract: the three halves and the conjunction capstone ----

# ORDERED half: induction on t.  t=1+q peels one tick (ticks unfolds to
# ticks(q, tick_lanes(tick(ls, ps)), ps) definitionally); t=0 routes
# against ls itself, and the line index peels WITH the projection list
# (nth_line(route_all, 0) is the head route_proj definitionally), so the
# base is a ps/i induction whose head is exactly line_ordered and whose
# bounds witness kills the Nil case.
def routing_ordered_nil(+ls: List<&2, R.Lane>, ps: List<&2, R.Proj>, i: Nat,
                        h: R.lt_ok(i, R.projs_len(ps)))
  -> {Nat.is_le(R.l_i0(R.nth_line(R.tick_lines(R.ticks(0n, ls, ps)), i)),
                R.l_i1(R.nth_line(R.tick_lines(R.ticks(0n, ls, ps)), i))) == True{} : Bool}:
  match ps i h:
    case Nil{} _ h:
      Empty.absurd({Nat.is_le(R.l_i0(R.nth_line(R.route_all(ls, Nil{}), i)),
                               R.l_i1(R.nth_line(R.route_all(ls, Nil{}), i))) == True{} : Bool},
                   lt_ok_nil_absurd(i, h))
    case +p <> t 0n _:
      Laws.line_ordered(R.lane_newest(R.nth_lane(ls, R.proj_src(p))),
                        R.proj_d(p),
                        R.lane_num(R.nth_lane(ls, R.proj_src(p))),
                        R.lane_k(R.nth_lane(ls, R.proj_src(p))),
                        R.proj_win(p))
    case p <> t 1n+q hlt:
      routing_ordered_nil(ls, t, q, hlt)

def routing_ordered_go(t: Nat, +ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>,
                       i: Nat, hb: R.lt_ok(i, R.projs_len(ps)))
  -> {Nat.is_le(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                R.l_i1(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i))) == True{} : Bool}:
  match t:
    case 0n:
      routing_ordered_nil(ls, ps, i, hb)
    case 1n+q:
      routing_ordered_go(q, R.tick_lanes(R.tick(ls, ps)), ps, i, hb)

def Laws.routing_ordered(ls, ps, t, i, hb):
  routing_ordered_go(t, ls, ps, i, hb)

# IN-WINDOW, proj level (the weak form): read_window_lo gives
# n - horizon <= n - (d + win); the window's own head is n - d
# (read_i0_is_window_head); antitonicity orders n - (d + win) behind
# n - d; le_trans chains them.  Pure composition of proved bricks.
def routing_in_window_proj(+n: Nat, nlanes: Nat, +horizon: Nat, +p: R.Proj,
                            +num: Nat, +den: Nat,
                            +h: {R.proj_shape_ok(nlanes, horizon, p) == True{} : Bool})
    -> {Nat.is_le(Nat.sub(n, horizon),
                  R.l_i0(R.route_read(n, R.proj_d(p), num, den, R.proj_win(p)))) == True{} : Bool}:
  btrans(Nat.is_le(Nat.sub(n, horizon),
                   R.l_i0(R.route_read(n, R.proj_d(p), num, den, R.proj_win(p)))),
         Nat.is_le(Nat.sub(n, horizon),
                   R.win_hi(R.route_window(n, R.proj_d(p), R.proj_win(p)))),
         Equal.cong(Nat, Bool, x => Nat.is_le(Nat.sub(n, horizon), x),
                    R.l_i0(R.route_read(n, R.proj_d(p), num, den, R.proj_win(p))),
                    R.win_hi(R.route_window(n, R.proj_d(p), R.proj_win(p))),
                    Equal.sym(Nat,
                      R.win_hi(R.route_window(n, R.proj_d(p), R.proj_win(p))),
                      R.l_i0(R.route_read(n, R.proj_d(p), num, den, R.proj_win(p))),
                      Laws.read_i0_is_window_head(n, R.proj_d(p), num, den,
                                                  R.proj_win(p)))),
         Laws.le_trans(Nat.sub(n, horizon),
                       Nat.sub(n, Nat.add(R.proj_d(p), R.proj_win(p))),
                       Nat.sub(n, R.proj_d(p)),
                       Laws.read_window_lo(n, nlanes, horizon, p, h),
                       Laws.sub_antitone(n, R.proj_d(p),
                                         Nat.add(R.proj_d(p), R.proj_win(p)),
                                         le_add_r(R.proj_d(p), R.proj_win(p)))))

# IN-WINDOW half, tick level: the same t-induction; at t=0 the line
# index peels with the projection list, the head needs only the fold's
# head conjunct (projs_ok_cons), the tail recurses with the peeled
# bounds witness and the tail conjunct.
def routing_window_nil(+nlanes: Nat, +horizon: Nat, +ls: List<&2, R.Lane>,
                       ps: List<&2, R.Proj>, i: Nat, h: R.lt_ok(i, R.projs_len(ps)),
                       +hok: {R.projs_shape_ok(nlanes, horizon, ps) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(0n, ls, ps)),
                                                R.proj_src(R.nth_proj(ps, i)))), horizon),
                R.l_i0(R.nth_line(R.tick_lines(R.ticks(0n, ls, ps)), i))) == True{} : Bool}:
  match ps i h:
    case Nil{} _ h:
      Empty.absurd({Nat.is_le(Nat.sub(R.lane_newest(R.nth_lane(ls,
                                                    R.proj_src(R.nth_proj(Nil{}, i)))), horizon),
                               R.l_i0(R.nth_line(R.route_all(ls, Nil{}), i))) == True{} : Bool},
                   lt_ok_nil_absurd(i, h))
    case +p <> +t 0n _:
      routing_in_window_proj(R.lane_newest(R.nth_lane(ls, R.proj_src(p))),
                             nlanes, horizon, p,
                             R.lane_num(R.nth_lane(ls, R.proj_src(p))),
                             R.lane_k(R.nth_lane(ls, R.proj_src(p))),
                             and_elim_l_go(R.proj_shape_ok(nlanes, horizon, p),
                                           R.projs_shape_ok(nlanes, horizon, t),
                                           hok))
    case p <> t 1n+q hlt:
      routing_window_nil(nlanes, horizon, ls, t, q, hlt,
                         and_elim_r_go(R.proj_shape_ok(nlanes, horizon, p),
                                       R.projs_shape_ok(nlanes, horizon, t),
                                       hok))

def routing_window_tick_go(+nlanes: Nat, +horizon: Nat, t: Nat,
                           +ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>,
                           i: Nat, hb: R.lt_ok(i, R.projs_len(ps)),
                           +hok: {R.projs_shape_ok(nlanes, horizon, ps) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                                R.proj_src(R.nth_proj(ps, i)))),
                         horizon),
                R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i))) == True{} : Bool}:
  match t:
    case 0n:
      routing_window_nil(nlanes, horizon, ls, ps, i, hb, hok)
    case 1n+q:
      routing_window_tick_go(nlanes, horizon, q, R.tick_lanes(R.tick(ls, ps)),
                             ps, i, hb, hok)

def Laws.routing_in_window(nlanes, horizon, ls, ps, t, i, hb, hok):
  routing_window_tick_go(nlanes, horizon, t, ls, ps, i, hb, hok)

# THE CAPSTONE: and_intro over the three halves.  The in-window half's
# shape witness is ok(c)'s projs_shape_ok conjunct, transported from
# cfg_projs(c) to ps across the equality tie hps (cong on the fold).
def Laws.routing_contract(c, ls, ps, t, i, h, hls, hps, hb):
  # hb is a Type witness (not +able); the three halves each need it, so
  # convert it ONCE to the Bool form and back per use (le_ok_iff / b_le).
  +hbB = Laws.le_ok_iff(Nat.add(i, 1n), R.projs_len(ps), hb)
  hok_ps = btrans(R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c), ps),
                  R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
                                   R.cfg_projs(c)),
                  Equal.cong(List<&2, R.Proj>, Bool,
                    xs => R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)),
                                           R.cfg_horizon(c), xs),
                    ps, R.cfg_projs(c), hps),
                  Laws.ok_projs(c, h))
  and_intro(Nat.is_le(R.l_i1(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                      R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                                R.proj_src(R.nth_proj(ps, i))))),
            Bool.and(Nat.is_le(Nat.sub(R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                                               R.proj_src(R.nth_proj(ps, i)))),
                                       R.cfg_horizon(c)),
                               R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i))),
                     Nat.is_le(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                               R.l_i1(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)))),
            Laws.read_fresh_ticks(ls, ps, t, i, b_le(Nat.add(i, 1n), R.projs_len(ps), hbB)),
            and_intro(Nat.is_le(Nat.sub(R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                                               R.proj_src(R.nth_proj(ps, i)))),
                                        R.cfg_horizon(c)),
                                R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i))),
                      Nat.is_le(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                                R.l_i1(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i))),
                      Laws.routing_in_window(R.nats_len(R.cfg_lanes(c)),
                                             R.cfg_horizon(c), ls, ps, t, i,
                                             b_le(Nat.add(i, 1n), R.projs_len(ps), hbB),
                                             hok_ps),
                      Laws.routing_ordered(ls, ps, t, i,
                                           b_le(Nat.add(i, 1n), R.projs_len(ps), hbB))))

# --------------------------------------------------------------------------
# 8b. the memory contract ladder: mod_succ_le, add_le_mono_r,
#     ring_write_len_succ, read_window_add (sharp), routing_window_add,
#     ring_correspondence, memory_contract
# --------------------------------------------------------------------------

# ---- mod_succ_le: the one-tick slot bound, via the mm twin ----
# PL(n, m, r): the slot after 1+n ticks is at most one past the slot
# after n ticks.  One induction over (n, m); the +n case peels one tick
# off both machines (the wrap hands m's role to r, the normal tick
# charges r by one), each case IS the hypothesis.
def mod_succ_le_pl(n: Nat, m: Nat, r: Nat)
  -> {Nat.is_le(Pair.snd(Nat, Nat, mm(Nat.add(1n, n), m, r)),
                Nat.add(1n, Pair.snd(Nat, Nat, mm(n, m, r)))) == True{} : Bool}:
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+mp:
      Laws.le_refl_b(r)
    case 1n+np 0n:
      mod_succ_le_pl(np, r, 0n)
    case 1n+np 1n+mp:
      mod_succ_le_pl(np, mp, 1n+r)

# the law form: bridge both mods to the twin with go_state, then PL.
# Both rewrites go FROM the go-machine terms TO the twin terms (the
# chain is the btrans equality {law-goal == PL-goal}), so go_state is
# used directly, no sym.
def Laws.mod_succ_le(n, cp):
  btrans(Nat.is_le(Nat.mod(Nat.add(1n, n), 1n+cp),
                   Nat.add(1n, Nat.mod(n, 1n+cp))),
         Nat.is_le(Pair.snd(Nat, Nat, mm(Nat.add(1n, n), cp, 0n)),
                   Nat.add(1n, Pair.snd(Nat, Nat, mm(n, cp, 0n)))),
         Equal.trans(Bool,
           Nat.is_le(Nat.mod(Nat.add(1n, n), 1n+cp),
                     Nat.add(1n, Nat.mod(n, 1n+cp))),
           Nat.is_le(Pair.snd(Nat, Nat, mm(Nat.add(1n, n), cp, 0n)),
                     Nat.add(1n, Nat.mod(n, 1n+cp))),
           Nat.is_le(Pair.snd(Nat, Nat, mm(Nat.add(1n, n), cp, 0n)),
                     Nat.add(1n, Pair.snd(Nat, Nat, mm(n, cp, 0n)))),
           Equal.cong(Nat, Bool, x => Nat.is_le(x, Nat.add(1n, Nat.mod(n, 1n+cp))),
                      Nat.mod(Nat.add(1n, n), 1n+cp),
                      Pair.snd(Nat, Nat, mm(Nat.add(1n, n), cp, 0n)),
                      go_state(Nat.add(1n, n), cp, 0n, 0n)),
           Equal.cong(Nat, Bool,
                      x => Nat.is_le(Pair.snd(Nat, Nat, mm(Nat.add(1n, n), cp, 0n)), x),
                      Nat.add(1n, Nat.mod(n, 1n+cp)),
                      Nat.add(1n, Pair.snd(Nat, Nat, mm(n, cp, 0n))),
                      Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                                 Nat.mod(n, 1n+cp),
                                 Pair.snd(Nat, Nat, mm(n, cp, 0n)),
                                 go_state(n, cp, 0n, 0n)))),
         mod_succ_le_pl(n, cp, 0n))

# ---- add_le_mono_r: induction on a; the succ case peels one successor
# off both sums, the base is the hypothesis itself (add(0, x) == x).
def add_le_mono_r_go(a: Nat, b: Nat, c: Nat,
                     +h: {Nat.is_le(b, c) == True{} : Bool})
    -> {Nat.is_le(Nat.add(a, b), Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      h
    case 1n+a2:
      add_le_mono_r_go(a2, b, c, h)

def Laws.add_le_mono_r(a, b, c, h):
  add_le_mono_r_go(a, b, c, h)

# ---- ring_write_len_succ: induction on (xs, s).  The extension case
# (s = 0 at Nil / at the spine's end) computes; the overwrite case
# recurses with the peeled witness, the goal peeling one successor on
# both sides in lockstep.
def ring_write_len_succ_go(+xs: List<&2, F32>, +v: F32, s: Nat,
                           h: R.le_ok(s, H.hist_len(xs)))
  -> {Nat.is_le(Nat.add(1n, s),
                H.hist_len(H.ring_write(xs, v, s))) == True{} : Bool}:
  match xs s h:
    case Nil{} 0n _:
      {==}
    case Nil{} 1n+p h:
      Empty.absurd({Nat.is_le(Nat.add(1n, 1n+p),
                              H.hist_len(H.ring_write(Nil{}, v, 1n+p))) == True{} : Bool},
                   le_succ_zero_absurd(p, h))
    case h <> t 0n _:
      le_zero(H.hist_len(t))
    case h <> t 1n+p h:
      ring_write_len_succ_go(t, v, p, h)

def Laws.ring_write_len_succ(xs, v, s, h):
  ring_write_len_succ_go(xs, v, s, h)

# ---- the accumulator invariant step: the write at tick tk's slot keeps
# the invariant valid at tick 1+tk -- mod_succ_le bounds the next slot
# by one past the current, ring_write_len_succ keeps the accumulator at
# least that long.
def hwinv_step(+cp: Nat, +tk: Nat, +acc: List<&2, F32>, +v: F32,
               h: R.le_ok(Nat.mod(tk, 1n+cp), H.hist_len(acc)))
  -> R.le_ok(Nat.mod(Nat.add(1n, tk), 1n+cp),
             H.hist_len(H.ring_write(acc, v, Nat.mod(tk, 1n+cp)))):
  b_le(Nat.mod(Nat.add(1n, tk), 1n+cp),
       H.hist_len(H.ring_write(acc, v, Nat.mod(tk, 1n+cp))),
       Laws.le_trans(Nat.mod(Nat.add(1n, tk), 1n+cp),
                     Nat.add(1n, Nat.mod(tk, 1n+cp)),
                     H.hist_len(H.ring_write(acc, v, Nat.mod(tk, 1n+cp))),
                     Laws.mod_succ_le(tk, cp),
                     Laws.ring_write_len_succ(acc, v, Nat.mod(tk, 1n+cp), h)))

# ---- read_window_add (the SHARP window bound) ----
# sub_zero_sat: when n < d, the saturating sub answers 0 (by joint
# induction, the over-long witness dying on its own Empty arms).
def sub_zero_sat(n: Nat, d: Nat, h: R.le_ok(Nat.add(1n, n), d))
  -> {Nat.sub(n, d) == 0n : Nat}:
  match n d h:
    case 0n 0n h:
      {==}
    case 0n 1n+q h:
      {==}
    case 1n+p 0n h:
      Empty.absurd({Nat.sub(1n+p, 0n) == 0n : Nat}, h)
    case 1n+p 1n+q h:
      sub_zero_sat(p, q, h)

# read_window_add: case on d.  d=0 clamps i0 to n, and 1 + n <= n +
# horizon is one add_le_mono_r away (1 <= horizon IS the hypothesis).
# d = 1+dp splits by trichotomy against n: inside (d <= n), the
# cancellation (n - d) + d == n regroups 1 + n into (n-d) + (d+1),
# which add_le_mono_r (at d + 1 <= horizon, the hypothesis itself)
# bounds by (n-d) + horizon; outside (n < d), the sub saturates to 0
# (sub_zero_sat) and d + 1 <= horizon exceeds n + 1 outright.
def read_window_add_go(+n: Nat, +d: Nat, +num: Nat, +den: Nat, +win: Nat,
                       +horizon: Nat,
                       +h: {Nat.is_le(Nat.add(d, 1n), horizon) == True{} : Bool})
  -> {Nat.is_le(Nat.add(1n, n),
                Nat.add(R.l_i0(R.route_read(n, d, num, den, win)),
                        horizon)) == True{} : Bool}:
  match d:
    case 0n:
      btrans(Nat.is_le(Nat.add(1n, n), Nat.add(n, horizon)),
             Nat.is_le(Nat.add(n, 1n), Nat.add(n, horizon)),
             Equal.cong(Nat, Bool, x => Nat.is_le(x, Nat.add(n, horizon)),
                        Nat.add(1n, n), Nat.add(n, 1n),
                        Laws.add_comm(1n, n)),
             Laws.add_le_mono_r(n, 1n, horizon, h))
    case 1n++dp:
      nat_cases(1n+dp, n,
        {Nat.is_le(Nat.add(1n, n),
                   Nat.add(R.l_i0(R.route_read(n, 1n+dp, num, den, win)),
                           horizon)) == True{} : Bool},
        wkle =>
          btrans(Nat.is_le(Nat.add(1n, n),
                           Nat.add(Nat.sub(n, 1n+dp), horizon)),
                 Nat.is_le(Nat.add(Nat.sub(n, 1n+dp), Nat.add(1n+dp, 1n)),
                           Nat.add(Nat.sub(n, 1n+dp), horizon)),
                 Equal.cong(Nat, Bool,
                            x => Nat.is_le(x, Nat.add(Nat.sub(n, 1n+dp), horizon)),
                            Nat.add(1n, n),
                            Nat.add(Nat.sub(n, 1n+dp), Nat.add(1n+dp, 1n)),
                            Equal.trans(Nat,
                              Nat.add(1n, n),
                              Nat.add(n, 1n),
                              Nat.add(Nat.sub(n, 1n+dp), Nat.add(1n+dp, 1n)),
                              Laws.add_comm(1n, n),
                              Equal.trans(Nat,
                                Nat.add(n, 1n),
                                Nat.add(Nat.add(Nat.sub(n, 1n+dp), 1n+dp), 1n),
                                Nat.add(Nat.sub(n, 1n+dp), Nat.add(1n+dp, 1n)),
                                Equal.sym(Nat,
                                  Nat.add(Nat.add(Nat.sub(n, 1n+dp), 1n+dp), 1n),
                                  Nat.add(n, 1n),
                                  Equal.cong(Nat, Nat, x => Nat.add(x, 1n),
                                             Nat.add(Nat.sub(n, 1n+dp), 1n+dp),
                                             n,
                                             Laws.sub_add_cancel(n, 1n+dp,
                                               Laws.le_ok_iff(1n+dp, n, wkle)))),
                                Laws.add_assoc(Nat.sub(n, 1n+dp), 1n+dp, 1n)))),
                 Laws.add_le_mono_r(Nat.sub(n, 1n+dp), Nat.add(1n+dp, 1n),
                                    horizon, h)),
        wkgt =>
          # wkgt is a Type witness used twice (saturation + the succ
          # step); round-trip it once through the Bool form
          +wB = Laws.le_ok_iff(Nat.add(1n, n), 1n+dp, wkgt)
          btrans(Nat.is_le(Nat.add(1n, n),
                           Nat.add(Nat.sub(n, 1n+dp), horizon)),
                 Nat.is_le(Nat.add(1n, n), horizon),
                 Equal.cong(Nat, Bool,
                            x => Nat.is_le(Nat.add(1n, n), Nat.add(x, horizon)),
                            Nat.sub(n, 1n+dp), 0n,
                            sub_zero_sat(n, 1n+dp,
                                         b_le(Nat.add(1n, n), 1n+dp, wB))),
                 Laws.le_trans(Nat.add(1n, n), Nat.add(1n+dp, 1n), horizon,
                   btrans(Nat.is_le(Nat.add(1n, n), Nat.add(1n+dp, 1n)),
                          Nat.is_le(Nat.add(1n, n), Nat.add(1n, 1n+dp)),
                          Equal.cong(Nat, Bool, x => Nat.is_le(Nat.add(1n, n), x),
                                     Nat.add(1n+dp, 1n), Nat.add(1n, 1n+dp),
                                     Laws.add_comm(1n+dp, 1n)),
                          Laws.le_succ_of_le(Nat.add(1n, n), 1n+dp, wB)),
                   h)))

def Laws.read_window_add(n, d, num, den, win, horizon, h):
  read_window_add_go(n, d, num, den, win, horizon, h)

# ---- routing_window_add: the sharp bound at tick state ----
# Same two-level structure as routing_in_window: ps/i peeling at t=0
# (the head needs only the fold's head conjunct, via proj_delay_fits),
# t-induction above it.
def routing_window_add_nil(+nlanes: Nat, +horizon: Nat, +ls: List<&2, R.Lane>,
                           ps: List<&2, R.Proj>, i: Nat,
                           h: R.lt_ok(i, R.projs_len(ps)),
                           +hok: {R.projs_shape_ok(nlanes, horizon, ps) == True{} : Bool})
  -> {Nat.is_le(Nat.add(1n,
                        R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(0n, ls, ps)),
                                                 R.proj_src(R.nth_proj(ps, i))))),
                Nat.add(R.l_i0(R.nth_line(R.tick_lines(R.ticks(0n, ls, ps)), i)),
                        horizon)) == True{} : Bool}:
  match ps i h:
    case Nil{} _ h:
      Empty.absurd({Nat.is_le(Nat.add(1n,
                                      R.lane_newest(R.nth_lane(ls,
                                        R.proj_src(R.nth_proj(Nil{}, i))))),
                                      Nat.add(R.l_i0(R.nth_line(R.route_all(ls, Nil{}), i)),
                                              horizon)) == True{} : Bool},
                   lt_ok_nil_absurd(i, h))
    case +p <> +t 0n _:
      Laws.read_window_add(R.lane_newest(R.nth_lane(ls, R.proj_src(p))),
                           R.proj_d(p),
                           R.lane_num(R.nth_lane(ls, R.proj_src(p))),
                           R.lane_k(R.nth_lane(ls, R.proj_src(p))),
                           R.proj_win(p), horizon,
                           Laws.proj_delay_fits(nlanes, horizon, p,
                                           and_elim_l_go(R.proj_shape_ok(nlanes, horizon, p),
                                                         R.projs_shape_ok(nlanes, horizon, t),
                                                         hok)))
    case p <> t 1n+q hlt:
      routing_window_add_nil(nlanes, horizon, ls, t, q, hlt,
                             and_elim_r_go(R.proj_shape_ok(nlanes, horizon, p),
                                           R.projs_shape_ok(nlanes, horizon, t),
                                           hok))

def routing_window_add_tick_go(+nlanes: Nat, +horizon: Nat, t: Nat,
                               +ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>,
                               i: Nat, hb: R.lt_ok(i, R.projs_len(ps)),
                               +hok: {R.projs_shape_ok(nlanes, horizon, ps) == True{} : Bool})
  -> {Nat.is_le(Nat.add(1n,
                        R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                                 R.proj_src(R.nth_proj(ps, i))))),
                Nat.add(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                        horizon)) == True{} : Bool}:
  match t:
    case 0n:
      routing_window_add_nil(nlanes, horizon, ls, ps, i, hb, hok)
    case 1n+q:
      routing_window_add_tick_go(nlanes, horizon, q, R.tick_lanes(R.tick(ls, ps)),
                                 ps, i, hb, hok)

def Laws.routing_window_add(nlanes, horizon, ls, ps, t, i, hb, hok):
  routing_window_add_tick_go(nlanes, horizon, t, ls, ps, i, hb, hok)

# ---- ring_correspondence: the fold-stability lemma and the go-induction ----
#
# fold_stable_go: the fold over xs starting at tick tk2 does not disturb
# the read at the guarded slot mod(m, cap).  Invariants: heq (tk2 ==
# m + d, d the current write-tick's distance from the guarded tick m),
# hbd (len(xs) + d <= 1 + cp: every remaining write is within a lap of
# m), hd1 (1 <= d), hwinv (the accumulator invariant: the write at
# tk2's slot is within the accumulator's length).  The step: the head's
# write at slot mod(tk2, cap) differs from the guarded slot
# (mod_inj_lap at distance d, transported across heq), so
# ring_write_stable keeps the guarded read; the tail recurses with all
# four invariants advanced (hwinv_step for the length, add_succ for the
# tick/distance regrouping).
def fold_stable_go(+xs: List<&2, F32>, +cp: Nat, +tk2: Nat, +m: Nat, +d: Nat,
                   +acc: List<&2, F32>, +ic: F32,
                   +heq: {Nat.add(m, d) == tk2 : Nat},
                   hbd: R.le_ok(Nat.add(H.hist_len(xs), d), 1n+cp),
                   hd1: R.le_ok(1n, d),
                   hwinv: R.le_ok(Nat.mod(tk2, 1n+cp), H.hist_len(acc)))
  -> {H.hist_read(H.ring_of_go(xs, 1n+cp, tk2, acc), Nat.mod(m, 1n+cp), ic)
      == H.hist_read(acc, Nat.mod(m, 1n+cp), ic) : F32}:
  match xs:
    case Nil{}:
      {==}
    case hh <> tt:
      # the Type witnesses hbd/hwinv are each used twice (extraction +
      # advancement): round-trip once through the Bool form
      +hbdB = Laws.le_ok_iff(Nat.add(H.hist_len(tt), d), cp, hbd)
      +hwinvB = Laws.le_ok_iff(Nat.mod(tk2, 1n+cp), H.hist_len(acc), hwinv)
      # the per-write distance bound d <= cp (from len(tt) + d <= cp and
      # d <= len(tt) + d)
      h2 = Laws.le_trans(d, Nat.add(H.hist_len(tt), d), cp,
        btrans(Nat.is_le(d, Nat.add(H.hist_len(tt), d)),
               Nat.is_le(d, Nat.add(d, H.hist_len(tt))),
               Equal.cong(Nat, Bool, x => Nat.is_le(d, x),
                          Nat.add(H.hist_len(tt), d),
                          Nat.add(d, H.hist_len(tt)),
                          Laws.add_comm(H.hist_len(tt), d)),
               le_add_r(d, H.hist_len(tt))),
        hbdB)
      # the write at tick tk2 hits a different slot than mod(m, cap)
      hne = ne_symm(Nat.mod(tk2, 1n+cp), Nat.mod(m, 1n+cp),
        btrans(Nat.is_ne(Nat.mod(tk2, 1n+cp), Nat.mod(m, 1n+cp)),
               Nat.is_ne(Nat.mod(Nat.add(m, d), 1n+cp), Nat.mod(m, 1n+cp)),
               Equal.cong(Nat, Bool, x => Nat.is_ne(Nat.mod(x, 1n+cp),
                                                    Nat.mod(m, 1n+cp)),
                          tk2, Nat.add(m, d),
                          Equal.sym(Nat, Nat.add(m, d), tk2, heq)),
               Laws.mod_inj_lap(m, d, cp,
                                Laws.le_ok_iff(1n, d, hd1), h2)))
      Equal.trans(F32,
        H.hist_read(H.ring_of_go(tt, 1n+cp, Nat.add(1n, tk2),
                                 H.ring_write(acc, hh, Nat.mod(tk2, 1n+cp))),
                    Nat.mod(m, 1n+cp), ic),
        H.hist_read(H.ring_write(acc, hh, Nat.mod(tk2, 1n+cp)),
                    Nat.mod(m, 1n+cp), ic),
        H.hist_read(acc, Nat.mod(m, 1n+cp), ic),
        fold_stable_go(tt, cp, Nat.add(1n, tk2), m, Nat.add(1n, d),
                       H.ring_write(acc, hh, Nat.mod(tk2, 1n+cp)), ic,
          Equal.trans(Nat, Nat.add(m, Nat.add(1n, d)),
            1n+Nat.add(m, d), Nat.add(1n, tk2),
            Laws.add_succ(m, d),
            Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                       Nat.add(m, d), tk2, heq)),
          b_le(Nat.add(H.hist_len(tt), Nat.add(1n, d)), 1n+cp,
            btrans(Nat.is_le(Nat.add(H.hist_len(tt), Nat.add(1n, d)), 1n+cp),
                   Nat.is_le(Nat.add(H.hist_len(tt), d), cp),
                   Equal.trans(Bool,
                     Nat.is_le(Nat.add(H.hist_len(tt), Nat.add(1n, d)), 1n+cp),
                     Nat.is_le(Nat.add(1n, Nat.add(H.hist_len(tt), d)), 1n+cp),
                     Nat.is_le(Nat.add(H.hist_len(tt), d), cp),
                     Equal.cong(Nat, Bool, x => Nat.is_le(x, 1n+cp),
                                Nat.add(H.hist_len(tt), Nat.add(1n, d)),
                                Nat.add(1n, Nat.add(H.hist_len(tt), d)),
                                Laws.add_succ(H.hist_len(tt), d)),
                     {==}),
                   hbdB)),
          Unit{},
          hwinv_step(cp, tk2, acc, hh,
                     b_le(Nat.mod(tk2, 1n+cp), H.hist_len(acc), hwinvB))),
        Laws.ring_write_stable(acc, hh, ic, Nat.mod(m, 1n+cp),
                               Nat.mod(tk2, 1n+cp), hne,
                               b_le(Nat.mod(tk2, 1n+cp), H.hist_len(acc),
                                    hwinvB)))

# ring_corr_go: the generalized correspondence.  The tape peels from the
# FRONT while the read's ABSOLUTE tick j = tk + off stays fixed: off
# peels with the tape, the window witnesses (lt_ok(off, len) and
# le_ok(len, off + cap)) peel one successor each, and the accumulator
# invariant advances by hwinv_step.  off = 0 is the head case: the fold
# has just written the head at slot mod(tk, cap) (write-read, witness
# hwinv) and the remaining fold cannot disturb that slot (fold_stable,
# lap bound len(t) <= cp from the window witness at off = 0).
def ring_corr_go(+xs: List<&2, F32>, +cp: Nat, +tk: Nat, +acc: List<&2, F32>,
                 +ic: F32, off: Nat,
                 hj: R.lt_ok(off, H.hist_len(xs)),
                 hw: R.le_ok(H.hist_len(xs), Nat.add(off, 1n+cp)),
                 hwinv: R.le_ok(Nat.mod(tk, 1n+cp), H.hist_len(acc)))
  -> {H.hist_read(H.ring_of_go(xs, 1n+cp, tk, acc),
                  Nat.mod(Nat.add(tk, off), 1n+cp), ic)
      == H.hist_read(xs, off, ic) : F32}:
  match xs off:
    case Nil{} 0n:
      Empty.absurd({H.hist_read(H.ring_of_go(Nil{}, 1n+cp, tk, acc),
                                Nat.mod(Nat.add(tk, 0n), 1n+cp), ic)
                    == H.hist_read(Nil{}, 0n, ic) : F32},
                   lt_ok_nil_absurd(off, hj))
    case Nil{} 1n+q:
      Empty.absurd({H.hist_read(H.ring_of_go(Nil{}, 1n+cp, tk, acc),
                                Nat.mod(Nat.add(tk, 1n+q), 1n+cp), ic)
                    == H.hist_read(Nil{}, 1n+q, ic) : F32},
                   lt_ok_nil_absurd(off, hj))
    case h <> t 0n:
      # hwinv is used twice (write-read + the fold's invariant): Bool it
      +hwinvB = Laws.le_ok_iff(Nat.mod(tk, 1n+cp), H.hist_len(acc), hwinv)
      # the fold's lap bound, from the window witness at off = 0:
      # len(t) <= cp (hw peels to exactly that)
      hbd0 = b_le(Nat.add(H.hist_len(t), 1n), 1n+cp,
        btrans(Nat.is_le(Nat.add(H.hist_len(t), 1n), 1n+cp),
               Nat.is_le(H.hist_len(t), cp),
               Equal.trans(Bool,
                 Nat.is_le(Nat.add(H.hist_len(t), 1n), 1n+cp),
                 Nat.is_le(Nat.add(1n, H.hist_len(t)), 1n+cp),
                 Nat.is_le(H.hist_len(t), cp),
                 Equal.cong(Nat, Bool, x => Nat.is_le(x, 1n+cp),
                            Nat.add(H.hist_len(t), 1n),
                            Nat.add(1n, H.hist_len(t)),
                            Laws.add_one(H.hist_len(t))),
                 {==}),
               Laws.le_ok_iff(H.hist_len(t), cp, hw)))
      Equal.trans(F32,
        H.hist_read(H.ring_of_go(t, 1n+cp, Nat.add(1n, tk),
                                 H.ring_write(acc, h, Nat.mod(tk, 1n+cp))),
                    Nat.mod(Nat.add(tk, 0n), 1n+cp), ic),
        H.hist_read(H.ring_of_go(t, 1n+cp, Nat.add(1n, tk),
                                 H.ring_write(acc, h, Nat.mod(tk, 1n+cp))),
                    Nat.mod(tk, 1n+cp), ic),
        h,
        Equal.cong(Nat, F32,
          z => H.hist_read(H.ring_of_go(t, 1n+cp, Nat.add(1n, tk),
                           H.ring_write(acc, h, Nat.mod(tk, 1n+cp))), z, ic),
          Nat.mod(Nat.add(tk, 0n), 1n+cp), Nat.mod(tk, 1n+cp),
          Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+cp),
                     Nat.add(tk, 0n), tk, Laws.add_zero(tk))),
        Equal.trans(F32,
          H.hist_read(H.ring_of_go(t, 1n+cp, Nat.add(1n, tk),
                                   H.ring_write(acc, h, Nat.mod(tk, 1n+cp))),
                      Nat.mod(tk, 1n+cp), ic),
          H.hist_read(H.ring_write(acc, h, Nat.mod(tk, 1n+cp)),
                      Nat.mod(tk, 1n+cp), ic),
          h,
          fold_stable_go(t, cp, Nat.add(1n, tk), tk, 1n,
                         H.ring_write(acc, h, Nat.mod(tk, 1n+cp)), ic,
            Laws.add_comm(tk, 1n),
            hbd0,
            Unit{},
            hwinv_step(cp, tk, acc, h,
                       b_le(Nat.mod(tk, 1n+cp), H.hist_len(acc), hwinvB))),
          Laws.ring_write_read(acc, h, ic, Nat.mod(tk, 1n+cp),
                               b_le(Nat.mod(tk, 1n+cp), H.hist_len(acc),
                                    hwinvB))))
    case h <> t 1n++q:
      Equal.trans(F32,
        H.hist_read(H.ring_of_go(t, 1n+cp, Nat.add(1n, tk),
                                 H.ring_write(acc, h, Nat.mod(tk, 1n+cp))),
                    Nat.mod(Nat.add(tk, 1n+q), 1n+cp), ic),
        H.hist_read(H.ring_of_go(t, 1n+cp, Nat.add(1n, tk),
                                 H.ring_write(acc, h, Nat.mod(tk, 1n+cp))),
                    Nat.mod(Nat.add(Nat.add(1n, tk), q), 1n+cp), ic),
        H.hist_read(t, q, ic),
        Equal.cong(Nat, F32,
          z => H.hist_read(H.ring_of_go(t, 1n+cp, Nat.add(1n, tk),
                           H.ring_write(acc, h, Nat.mod(tk, 1n+cp))), z, ic),
          Nat.mod(Nat.add(tk, 1n+q), 1n+cp),
          Nat.mod(Nat.add(Nat.add(1n, tk), q), 1n+cp),
          Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+cp),
                     Nat.add(tk, 1n+q), Nat.add(Nat.add(1n, tk), q),
                     Laws.add_succ(tk, q))),
        ring_corr_go(t, cp, Nat.add(1n, tk),
                     H.ring_write(acc, h, Nat.mod(tk, 1n+cp)), ic, q,
                     hj, hw,
                     hwinv_step(cp, tk, acc, h, hwinv)))

# cap = 0 is vacuous: len <= j + 0 and j < len contradict.  The tape and
# j peel together, each case dying on its own witness.
def ring_corr_cap0(tape: List<&2, F32>, j: Nat,
                   hj: R.lt_ok(j, H.hist_len(tape)),
                   hw: R.le_ok(H.hist_len(tape), Nat.add(j, 0n))) -> Empty:
  match tape j:
    case Nil{} 0n:
      hj
    case Nil{} 1n+q:
      hj
    case h <> t 0n:
      hw
    case h <> t 1n+q:
      ring_corr_cap0(t, q, hj, hw)

def Laws.ring_correspondence(tape, cap, ic, j, hj, hw):
  match cap:
    case 0n:
      Empty.absurd({H.ring_read(H.ring_of(tape, 0n), j, 0n, ic)
                    == H.hist_read(tape, j, ic) : F32},
                   ring_corr_cap0(tape, j, hj, hw))
    case 1n+cp:
      ring_corr_go(tape, cp, 0n, Nil{}, ic, j, hj, hw, Unit{})

# x <= p lifts across a successor on BOTH sides: x+1 <= 1+p.  The
# le_lt_succ form gives x < 1+p; the ring's live-window witness wants
# the le form with the successors explicit on both sides (lt_ok is
# le_ok of j+1 against the tape length, tied to 1+newest).
def le_add_succ_both(x: Nat, p: Nat, h: {Nat.is_le(x, p) == True{} : Bool})
    -> {Nat.is_le(Nat.add(x, 1n), Nat.add(1n, p)) == True{} : Bool}:
  match x p:
    case 0n 0n:
      {==}
    case 0n 1n+s:
      {==}
    case 1n+r 0n:
      Bool.fne({Nat.is_le(Nat.add(1n+r, 1n), Nat.add(1n, 0n)) == True{} : Bool}, h)
    case 1n+r 1n+s:
      le_add_succ_both(r, s, h)

# ---- memory_contract: the composed capstone ----
# The endpoint j = i0 of the routed line lies inside the tape's live
# window: below, j <= i1 <= newest (ordered + fresh), and newest < len
# by the tape tie; above, the sharp window bound (routing_window_add)
# gives 1 + newest <= j + horizon, ok_cap's horizon <= cap lifts it to
# 1 + newest <= j + cap (add_le_mono_r), and the tape tie rewrites it
# to len <= j + cap.  ring_correspondence then delivers the slot's leaf.
def Laws.memory_contract(c, cap, tape, ic, ls, ps, t, i, h, hcap, hls, hps, hb,
                         htape):
  # hb (Type witness) is used by three lemmas: Bool it once
  +hbB = Laws.le_ok_iff(Nat.add(i, 1n), R.projs_len(ps), hb)
  hok_ps = btrans(R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c), ps),
                  R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
                                   R.cfg_projs(c)),
                  Equal.cong(List<&2, R.Proj>, Bool,
                    xs => R.projs_shape_ok(R.nats_len(R.cfg_lanes(c)),
                                           R.cfg_horizon(c), xs),
                    ps, R.cfg_projs(c), hps),
                  Laws.ok_projs(c, h))
  # j <= i1 <= newest
  hle = Laws.le_trans(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                      R.l_i1(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                      R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                               R.proj_src(R.nth_proj(ps, i)))),
                      Laws.routing_ordered(ls, ps, t, i,
                        b_le(Nat.add(i, 1n), R.projs_len(ps), hbB)),
                      Laws.read_fresh_ticks(ls, ps, t, i,
                        b_le(Nat.add(i, 1n), R.projs_len(ps), hbB)))
  # the live window's upper end: j + 1 <= len (via the tie)
  hj = b_le(Nat.add(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)), 1n),
            H.hist_len(tape),
    btrans(Nat.is_le(Nat.add(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)), 1n),
                     H.hist_len(tape)),
           Nat.is_le(Nat.add(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)), 1n),
                     Nat.add(1n, R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                                          R.proj_src(R.nth_proj(ps, i)))))),
           Equal.cong(Nat, Bool, x => Nat.is_le(Nat.add(R.l_i0(R.nth_line(
                        R.tick_lines(R.ticks(t, ls, ps)), i)), 1n), x),
                      H.hist_len(tape),
                      Nat.add(1n, R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                                           R.proj_src(R.nth_proj(ps, i))))),
                      htape),
           le_add_succ_both(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                      R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                               R.proj_src(R.nth_proj(ps, i)))),
                      hle)))
  # the live window's lower end: len <= j + cap (sharp bound + ok_cap)
  hw = b_le(H.hist_len(tape),
            Nat.add(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)), cap),
    btrans(Nat.is_le(H.hist_len(tape),
                     Nat.add(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)), cap)),
           Nat.is_le(Nat.add(1n, R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                                R.proj_src(R.nth_proj(ps, i))))),
                     Nat.add(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)), cap)),
           Equal.cong(Nat, Bool, x => Nat.is_le(x,
                        Nat.add(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)), cap)),
                      H.hist_len(tape),
                      Nat.add(1n, R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                                           R.proj_src(R.nth_proj(ps, i))))),
                      htape),
           Laws.le_trans(Nat.add(1n, R.lane_newest(R.nth_lane(R.tick_lanes(R.ticks(t, ls, ps)),
                                                    R.proj_src(R.nth_proj(ps, i))))),
                         Nat.add(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                                 R.cfg_horizon(c)),
                         Nat.add(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)), cap),
                         Laws.routing_window_add(R.nats_len(R.cfg_lanes(c)),
                                                 R.cfg_horizon(c), ls, ps, t, i,
                                                 b_le(Nat.add(i, 1n), R.projs_len(ps), hbB),
                                                 hok_ps),
                         Laws.add_le_mono_r(R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                                            R.cfg_horizon(c), cap,
                                            Laws.ok_cap_le(c, cap, hcap)))))
  Laws.ring_correspondence(tape, cap, ic,
                           R.l_i0(R.nth_line(R.tick_lines(R.ticks(t, ls, ps)), i)),
                           hj, hw)
