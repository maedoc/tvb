# PROOF_sweep.bend -- the proofs for LAWS_sweep.bend.  The gate:
#
#   bend PROOF_sweep.bend            must print ALL PROOFS CHECK
#   bend PROOF_sweep.bend --verdict  re-checked by the Lean-proved kernel
#
# House style (PROOF_router.bend): quantified laws go through go-lemmas
# that match the shrinking argument plus the witnesses; witness types
# (R.lt_ok / R.le_ok) refine by matching the Nat binders they speak about;
# `{==}` closes what normalises; Bool.fne refutes {False == True}
# hypotheses; Equal.cong lifts an equation under a context.
import Base
import ./LAWS_sweep.bend as Laws
import ./sweep.bend as S
import ./router.bend as R

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

# k < 0 is absurd: peeling k makes lt_ok(i, 0n) normalise to Empty in both
# cases (the mod_lt_zero_absurd pattern).
def lt_zero_absurd(i: Nat, h: R.lt_ok(i, 0n)) -> Empty:
  match i h:
    case 0n h:
      h
    case 1n+p h:
      h

# --------------------------------------------------------------------------
# Group 1 -- the row routing
# --------------------------------------------------------------------------
# sweep_nth_route: induction on k, peeling one row of the table per step.
# The witness lt_ok(k, len) refines with the peel: lt_ok(1+p, 1+len')
# normalises to lt_ok(p, len') (the add keeps the stuck shape take_nth
# relies on).  The Nil cases are absurd THROUGH the witness: a bounded k
# cannot index an empty table.

def sweep_nth_route_go(k: Nat, t: List<&2, F32>, h: R.lt_ok(k, S.sweep_len(t)))
  -> {S.sweep_nth(t, k) == S.sweep_word(t, k) : F32}:
  match k t h:
    case 0n Nil{} hlt:
      Empty.absurd({S.sweep_nth(Nil{}, 0n) == S.sweep_word(Nil{}, 0n) : F32}, hlt)
    case 0n h0 <> t _:
      {==}
    case 1n+p Nil{} hlt:
      Empty.absurd({S.sweep_nth(Nil{}, 1n+p) == S.sweep_word(Nil{}, 1n+p) : F32}, hlt)
    case 1n+p h0 <> t hlt:
      sweep_nth_route_go(p, t, hlt)

def Laws.sweep_nth_route(t, k, h):
  sweep_nth_route_go(k, t, h)

# the instances: pure computation on a literal table, definitional.
def Laws.sweep_nth_head(h, t):
  {==}

def Laws.sweep_nth_step(h, t, k):
  {==}

def Laws.sweep_route_inst_0():
  {==}

def Laws.sweep_route_inst_1():
  {==}

def Laws.sweep_route_inst_2():
  {==}

# --------------------------------------------------------------------------
# Group 2 -- the fan coverage
# --------------------------------------------------------------------------
# fan_lane_active: induction peeling n and k together; the ORIGINAL lane
# index k0 rides along unchanged (fan_lane_go applies f to k0, never to a
# shrunken index), so the step's goal is exactly the induction hypothesis.
# n = 0 with any k is absurd through the witness.

def fan_lane_active_go(n: Nat, k: Nat, k0: Nat, f: Nat -> String,
                       h: R.lt_ok(k, n))
  -> {S.fan_lane_go(n, k, k0, f) == f(k0) : String}:
  match n k h:
    case 0n 0n hlt:
      Empty.absurd({S.fan_lane_go(0n, 0n, k0, f) == f(k0) : String}, hlt)
    case 0n 1n+p hlt:
      Empty.absurd({S.fan_lane_go(0n, 1n+p, k0, f) == f(k0) : String}, hlt)
    case 1n+m 0n _:
      {==}
    case 1n+m 1n+p hlt:
      fan_lane_active_go(m, p, k0, f, hlt)

# the wrapper's k must appear twice (as the lane index AND the remembered
# original), so the doubling happens in a typed helper with a reusable +k;
# the law-filling def stays bare and single-use.
def fan_lane_active_wrap(n: Nat, +k: Nat, f: Nat -> String, h: R.lt_ok(k, n))
  -> {S.fan_lane(n, k, f) == f(k) : String}:
  fan_lane_active_go(n, k, k, f, h)

def Laws.fan_lane_active(n, k, f, h):
  fan_lane_active_wrap(n, k, f, h)

# fan_lane_inactive: the hypothesis {is_le(n, k) == True} rides along about
# the CURRENT (n, k), so it refines in lockstep with the peel:
# is_le(1+m, 1+p) normalises to is_le(m, p).  At k = 0 with n = 1+m the
# hypothesis is {is_le(1+m, 0) == True}, which normalises to
# {False == True} -- refuted with Bool.fne.

def fan_lane_inactive_go(n: Nat, k: Nat, k0: Nat, f: Nat -> String,
                         h: {Nat.is_le(n, k) == True{} : Bool})
  -> {S.fan_lane_go(n, k, k0, f) == "" : String}:
  match n k h:
    case 0n _ _:
      {==}
    case 1n+m 0n hlt:
      Bool.fne({S.fan_lane_go(1n+m, 0n, k0, f) == "" : String}, hlt)
    case 1n+m 1n+p hlt:
      fan_lane_inactive_go(m, p, k0, f, hlt)

def fan_lane_inactive_wrap(n: Nat, +k: Nat, f: Nat -> String,
                           h: {Nat.is_le(n, k) == True{} : Bool})
  -> {S.fan_lane(n, k, f) == "" : String}:
  fan_lane_inactive_go(n, k, k, f, h)

def Laws.fan_lane_inactive(n, k, f, h):
  fan_lane_inactive_wrap(n, k, f, h)

# fan8_exact: induction on the lane index i over the w-wide fan, peeling
# one lane of fan_go per step.  Two witnesses:
#   lt_ok(i, a)  -- the lane is active (an inactive lane's "" is NOT its
#                   run; the a = 0 arms are absurd through it);
#   le_ok(a, w)  -- the WIDTH witness, load-bearing at w = 0 with a > 0:
#                   the fan has silently dropped lanes there and the claim
#                   is false (this is the n_sweep > 8 failure mode).
# Runs may stay symbolic in the a = 0 arms and the i = 0 active arm: the
# fan cell is gate(a, str_nth(runs, 0n)), and gate at a constructor
# argument reduces without looking at runs.
def fan8_exact_go(w: Nat, a: Nat, runs: List<&2, String>, i: Nat,
                  hw: R.le_ok(a, w), h: R.lt_ok(i, a))
  -> {S.str_nth(S.fan_go(w, a, runs), i) == S.str_nth(runs, i) : String}:
  match w a runs i hw h:
    case 0n 0n rns _ _ hlt:
      Empty.absurd({S.str_nth(S.fan_go(0n, 0n, rns), i) == S.str_nth(rns, i) : String},
                   lt_zero_absurd(i, hlt))
    case 0n 1n+d rns _ hw _:
      Empty.absurd({S.str_nth(S.fan_go(0n, 1n+d, rns), i) == S.str_nth(rns, i) : String}, hw)
    case 1n+s 0n rns 0n _ hlt:
      Empty.absurd({S.str_nth(S.fan_go(1n+s, 0n, rns), 0n) == S.str_nth(rns, 0n) : String}, hlt)
    case 1n+s 0n rns 1n+p _ hlt:
      Empty.absurd({S.str_nth(S.fan_go(1n+s, 0n, rns), 1n+p) == S.str_nth(rns, 1n+p) : String}, hlt)
    case 1n+s 1n+d rns 0n _ _:
      {==}
    case 1n+s 1n+d r0 <> t 1n+p hw hlt:
      fan8_exact_go(s, d, t, p, hw, hlt)
    case 1n+s 1n+d Nil{} 1n+p hw hlt:
      fan8_exact_go(s, d, Nil{}, p, hw, hlt)

def Laws.fan8_exact(runs, n, k, hw, h):
  fan8_exact_go(8n, n, runs, k, hw, h)

# a = 0: every lane is inactive, so every read answers "" -- the all-zero
# fan needs no hypothesis (used by fan8_active's a = 0 arms).
def fan_go_zero_go(w: Nat, runs: List<&2, String>, i: Nat)
  -> {S.str_nth(S.fan_go(w, 0n, runs), i) == "" : String}:
  match w runs i:
    case 0n rns _:
      {==}
    case 1n+s rns 0n:
      {==}
    case 1n+s rns 1n+p:
      fan_go_zero_go(s, S.str_tail(rns), p)

# fan8_active: the inactive arm at the fan level.  The hypothesis
# {is_le(a, i) == True} rides along about the current (a, i) and refines
# with the peel; at an active lane (i = 0, a = 1+d) it normalises to
# {False == True} and is refuted.  No width witness needed: past the w
# lanes the read defaults to "" on both sides.
def fan8_active_go(w: Nat, a: Nat, runs: List<&2, String>, i: Nat,
                   h: {Nat.is_le(a, i) == True{} : Bool})
  -> {S.str_nth(S.fan_go(w, a, runs), i) == "" : String}:
  match w a runs i h:
    case 0n a rns i _:
      {==}
    case 1n+s 0n rns 0n _:
      {==}
    case 1n+s 0n rns 1n+p _:
      fan_go_zero_go(s, S.str_tail(rns), p)
    case 1n+s 1n+d rns 0n hlt:
      Bool.fne({S.str_nth(S.fan_go(1n+s, 1n+d, rns), 0n) == "" : String}, hlt)
    case 1n+s 1n+d r0 <> t 1n+p hlt:
      fan8_active_go(s, d, t, p, hlt)
    case 1n+s 1n+d Nil{} 1n+p hlt:
      fan8_active_go(s, d, Nil{}, p, hlt)

def Laws.fan8_active(runs, n, k, h):
  fan8_active_go(8n, n, runs, k, h)

# --------------------------------------------------------------------------
# Group 3 -- the gather
# --------------------------------------------------------------------------
# a = 0: the gathered fan is "" (each inactive lane contributes "" and
# "" ++ x reduces to x, so the goal normalises to the induction hypothesis
# itself).
def fan_gather_zero_go(w: Nat, runs: List<&2, String>)
  -> {S.gather(S.fan_go(w, 0n, runs)) == "" : String}:
  match w:
    case 0n:
      {==}
    case 1n+s:
      fan_gather_zero_go(s, S.str_tail(runs))

# fan_gather_order: induction on the lane count, peeling one lane per
# step.  The width witness le_ok(a, w) is load-bearing at w = 0 with a > 0
# (dropped lanes): the fan gathers "" while the sequential side still
# demands the dropped runs.  The step is a congruence: both sides
# normalise to r0 ++ rest, and the induction hypothesis equates the rests.
# The runs = Nil arm closes through the induction hypothesis too: the
# short table reads "" on both sides.
def fan_gather_order_go(w: Nat, a: Nat, runs: List<&2, String>,
                        hw: R.le_ok(a, w))
  -> {S.gather(S.fan_go(w, a, runs)) == S.seq_gather(a, runs) : String}:
  match w a runs hw:
    case 0n 0n rns _:
      {==}
    case 0n 1n+d rns hw:
      Empty.absurd({S.gather(S.fan_go(0n, 1n+d, rns)) == S.seq_gather(1n+d, rns) : String}, hw)
    case 1n+s 0n rns _:
      fan_gather_zero_go(s, S.str_tail(rns))
    case 1n+s 1n+d r0 <> t hw:
      Equal.cong(String, String, z => r0 ++ z,
                 S.gather(S.fan_go(s, d, t)), S.seq_gather(d, t),
                 fan_gather_order_go(s, d, t, hw))
    case 1n+s 1n+d Nil{} hw:
      fan_gather_order_go(s, d, Nil{}, hw)

def Laws.fan_gather_order(runs, n, hw):
  fan_gather_order_go(8n, n, runs, hw)
