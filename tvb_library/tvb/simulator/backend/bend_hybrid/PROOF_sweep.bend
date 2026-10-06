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
import ./PROOF_router.bend as PR

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

# the w = 8 instance of the engine's real 8-wide fan: the SAME go-lemma
# fan_exact's fill uses, at w = 8n (fills cannot call fills, so the
# instance repeats the one call; the shared induction is fan8_exact_go).
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

# the w = 8 instance -- the same go-lemma fan_gather_order_gen's fill
# uses, at w = 8n.
def Laws.fan_gather_order(runs, n, hw):
  fan_gather_order_go(8n, n, runs, hw)

# --------------------------------------------------------------------------
# Group 4 -- the composition
# --------------------------------------------------------------------------
# The validator's two conjuncts are and-eliminations (PR.and_elim_l_go /
# PR.and_elim_r_go, PROOF_router.bend's plain helpers, which re-export
# across module imports where filled laws do not).  sweep_valid_nth is
# fan8_exact with the width witness derived from sweep_ok_width (Bool
# form converted to the le_ok decider by PR.b_le).  The capstone chains
# three cong steps under Equal.trans -- one per component of the triple
# pair equality -- with the third component's proof the bridge call
# PR.routing_contract_at (Laws.routing_contract at the shared config,
# ties {==} since the law instantiates ls/ps definitionally).

def Laws.sweep_ok_width(t, c, h):
  PR.and_elim_l_go(Nat.is_le(S.sweep_len(t), 8n), R.ok(c), h)

def Laws.sweep_ok_cfg(t, c, h):
  PR.and_elim_r_go(Nat.is_le(S.sweep_len(t), 8n), R.ok(c), h)

def Laws.sweep_valid_nth(t, c, runs, h, k, hk):
  Laws.fan8_exact(runs, S.sweep_len(t), k,
                  PR.b_le(S.sweep_len(t), 8n,
                          PR.and_elim_l_go(Nat.is_le(S.sweep_len(t), 8n), R.ok(c), h)),
                  hk)

# the Type->Bool direction for a lt_ok witness (PR.le_ok_iff is a law
# fill and does not re-export, so its go-lemma is copied here): lt_ok(i, L)
# is definitionally le_ok(Nat.add(i, 1n), L), so the capstone calls this at
# (1n+i, L) with hk riding in as the le_ok witness.  One structural
# induction; the Empty arm is absurd through the witness, the x = 0n arms
# close by {==} (cmp(0n, _) is Lt, is_le(Lt) is True).
def sw_le_b_go(x: Nat, y: Nat, h: R.le_ok(x, y))
  -> {Nat.is_le(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      sw_le_b_go(p, q, h)

def sw_le_b(x: Nat, y: Nat, h: R.le_ok(x, y))
  -> {Nat.is_le(x, y) == True{} : Bool}:
  sw_le_b_go(x, y, h)

# the capstone.  h is needed twice (both conjunct eliminations), so it is
# re-bound + (equality proofs are Data: the le_ok_iff idiom).  hk is a
# Type-valued witness -- NOT +able -- so it is converted ONCE to its Bool
# form ({is_le(1n+i, len) == True}, exactly lt_ok(i, len) unfolded) and
# converted back per use with PR.b_le (the NOTES bool-witness idiom).
def Laws.sweep_contract(t, c, runs, tk, i, j, h, hk, hj):
  +h2 = h
  +hkB = sw_le_b(Nat.add(i, 1n), S.sweep_len(t), hk)
  hwB = PR.and_elim_l_go(Nat.is_le(S.sweep_len(t), 8n), R.ok(c), h)
  hok = PR.and_elim_r_go(Nat.is_le(S.sweep_len(t), 8n), R.ok(c), h2)
  hw = PR.b_le(S.sweep_len(t), 8n, hwB)
  hroute = Laws.sweep_nth_route(t, i,
                                PR.b_le(Nat.add(i, 1n), S.sweep_len(t), hkB))
  hfan = Laws.fan8_exact(runs, S.sweep_len(t), i, hw,
                         PR.b_le(Nat.add(i, 1n), S.sweep_len(t), hkB))
  hrun = PR.routing_contract_at(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c),
                                tk, j, hok, {==}, {==}, hj)
  Equal.trans(F32 & (String & Bool),
    (S.sweep_nth(t, i),
     S.str_nth(S.fan8(S.sweep_len(t), runs), i),
     S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
    (S.sweep_word(t, i),
     S.str_nth(S.fan8(S.sweep_len(t), runs), i),
     S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
    (S.sweep_word(t, i), S.str_nth(runs, i), True{}),
    Equal.cong(F32, F32 & (String & Bool),
               w => (w,
                     S.str_nth(S.fan8(S.sweep_len(t), runs), i),
                     S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
               S.sweep_nth(t, i), S.sweep_word(t, i), hroute),
    Equal.trans(F32 & (String & Bool),
      (S.sweep_word(t, i),
       S.str_nth(S.fan8(S.sweep_len(t), runs), i),
       S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
      (S.sweep_word(t, i), S.str_nth(runs, i),
       S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
      (S.sweep_word(t, i), S.str_nth(runs, i), True{}),
      Equal.cong(String, F32 & (String & Bool),
                 w => (S.sweep_word(t, i), w,
                       S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
                 S.str_nth(S.fan8(S.sweep_len(t), runs), i), S.str_nth(runs, i), hfan),
      Equal.cong(Bool, F32 & (String & Bool),
                 w => (S.sweep_word(t, i), S.str_nth(runs, i), w),
                 S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j),
                 True{}, hrun)))

# --------------------------------------------------------------------------
# Phase 3 -- the GENERALIZATION
# --------------------------------------------------------------------------
# A. GENERAL WIDTH.  fan8_exact_go and fan_gather_order_go were already
# written over the GENERAL fan_go (the w rides as a parameter), so the
# general laws are the same go-lemmas at abstract w -- no new induction.
# fan8_exact / fan_gather_order become what they always were: the w = 8
# instances of the engine's real 8-wide fan.

def Laws.fan_exact(runs, w, n, k, hw, h):
  fan8_exact_go(w, n, runs, k, hw, h)

def Laws.fan_gather_order_gen(runs, w, n, hw):
  fan_gather_order_go(w, n, runs, hw)

# --------------------------------------------------------------------------
# B. MULTI-PARAM ROWS
# --------------------------------------------------------------------------
# sweep_row_nth: the sweep_nth_route induction at the row level -- peel
# one row of the table per step; the witness refines with the peel; the
# Nil cases are absurd through the witness.

def sweep_row_nth_go(i: Nat, rows: List<&2, List<&2, F32>>,
                     h: R.lt_ok(i, S.rows_len(rows)))
  -> {S.sweep_row(rows, i) == S.sweep_row_ref(rows, i) : List<&2, F32>}:
  match i rows h:
    case 0n Nil{} hlt:
      Empty.absurd({S.sweep_row(Nil{}, 0n) == S.sweep_row_ref(Nil{}, 0n)
                    : List<&2, F32>}, hlt)
    case 0n h0 <> t _:
      {==}
    case 1n+p Nil{} hlt:
      Empty.absurd({S.sweep_row(Nil{}, 1n+p) == S.sweep_row_ref(Nil{}, 1n+p)
                    : List<&2, F32>}, hlt)
    case 1n+p h0 <> t hlt:
      sweep_row_nth_go(p, t, hlt)

def Laws.sweep_row_nth(rows, i, h):
  sweep_row_nth_go(i, rows, h)

# sweep_field_nth: sweep_nth_route instantiated at sim i's row -- the
# field read IS the row's word read.  The row witness rides unused (the
# claim is about the row the witness already routed).
def Laws.sweep_field_nth(rows, i, j, hi, hj):
  Laws.sweep_nth_route(S.sweep_row(rows, i), j, hj)

# --------------------------------------------------------------------------
# the row-major wire
# --------------------------------------------------------------------------
# the shift brick: reading at w + k equals dropping w elements first --
# skipping one row of the wire IS skipping w words of the read.  Peels w
# and the flat table in lockstep (the Nil case closes definitionally: both
# sides read the default).
def flat_shift_go(w: Nat, flat: List<&2, F32>, +k: Nat)
  -> {S.sweep_nth(flat, Nat.add(w, k))
      == S.sweep_nth(S.sweep_drop(flat, w), k) : F32}:
  match w flat:
    case 0n Nil{}:
      {==}
    case 0n h0 <> t:
      {==}
    case 1n+s Nil{}:
      {==}
    case 1n+s h0 <> t:
      flat_shift_go(s, t, k)

# flat_addr_step: Nat.mul(1n+i, w) reduces to w + i*w, so the goal is
# add(add(w, i*w), j) == add(w, (i*w + j)) -- exactly the add_assoc brick.
def Laws.flat_addr_step(i, w, j):
  PR.add_assoc_go(w, Nat.mul(i, w), j)

# flat_nth: induction on the row counter i.  The base is definitional
# (0*w + j reduces to j).  The step chains the address brick (row 1+i's
# field j lives at w + (i*w + j)), the shift brick (dropping the first row
# of w moves the read to that address), and the induction hypothesis at
# row i of the shrunken table; the goal's structural read reduces to the
# shrunken one.
def flat_nth_go(+w: Nat, i: Nat, +flat: List<&2, F32>, +j: Nat)
  -> {S.flat_at(flat, i, w, j) == S.flat_read(flat, i, w, j) : F32}:
  match i:
    case 0n:
      {==}
    case 1n+(+p):
      h1 = Equal.cong(Nat, F32, z => S.sweep_nth(flat, z),
                      S.flat_addr(1n+p, w, j),
                      Nat.add(w, S.flat_addr(p, w, j)),
                      Laws.flat_addr_step(p, w, j))
      h2 = flat_shift_go(w, flat, S.flat_addr(p, w, j))
      h3 = flat_nth_go(w, p, S.sweep_drop(flat, w), j)
      Equal.trans(F32,
        S.sweep_nth(flat, S.flat_addr(1n+p, w, j)),
        S.sweep_nth(flat, Nat.add(w, S.flat_addr(p, w, j))),
        S.flat_read_go(w, p, S.sweep_drop(flat, w), j),
        h1,
        Equal.trans(F32,
          S.sweep_nth(flat, Nat.add(w, S.flat_addr(p, w, j))),
          S.sweep_nth(S.sweep_drop(flat, w), S.flat_addr(p, w, j)),
          S.flat_read_go(w, p, S.sweep_drop(flat, w), j),
          h2, h3))

def Laws.flat_nth(flat, w, i, j):
  flat_nth_go(w, i, flat, j)

# --------------------------------------------------------------------------
# the column->row assembly
# --------------------------------------------------------------------------
# col_to_row: peel j and the column list in lockstep -- the assembled
# row's element j is column j's contribution by construction (element i of
# the j-th column), and past either end both sides read the default.
def col_to_row_go(j: Nat, cols: List<&2, List<&2, F32>>, +i: Nat)
  -> {S.sweep_nth(S.col_row(cols, i), j)
      == S.sweep_nth(S.col_nth(cols, j), i) : F32}:
  match j cols:
    case 0n Nil{}:
      {==}
    case 0n c0 <> rest:
      {==}
    case 1n+q Nil{}:
      {==}
    case 1n+q c0 <> rest:
      col_to_row_go(q, rest, i)

def Laws.col_to_row(cols, i, j):
  col_to_row_go(j, cols, i)

# the instance pins: pure computation on the literal 2x2 column table.
def Laws.col_row_inst_0():
  {==}

def Laws.col_row_inst_1():
  {==}

# --------------------------------------------------------------------------
# the row-table validator
# --------------------------------------------------------------------------
# the three and-elimination halves (PR.and_elim_l_go / PR.and_elim_r_go,
# PROOF_router.bend's plain helpers).  sweep_rows_ok is a NESTED and:
# width /\ (shape /\ ok), so the shape half eliminates twice.
def Laws.sweep_rows_ok_len(rows, wp, c, h):
  PR.and_elim_l_go(Nat.is_le(S.rows_len(rows), 8n),
                   Bool.and(S.rows_shape_ok(rows, wp), R.ok(c)), h)

def Laws.sweep_rows_ok_shape(rows, wp, c, h):
  PR.and_elim_l_go(S.rows_shape_ok(rows, wp), R.ok(c),
                   PR.and_elim_r_go(Nat.is_le(S.rows_len(rows), 8n),
                                    Bool.and(S.rows_shape_ok(rows, wp), R.ok(c)),
                                    h))

def Laws.sweep_rows_ok_cfg(rows, wp, c, h):
  PR.and_elim_r_go(S.rows_shape_ok(rows, wp), R.ok(c),
                   PR.and_elim_r_go(Nat.is_le(S.rows_len(rows), 8n),
                                    Bool.and(S.rows_shape_ok(rows, wp), R.ok(c)),
                                    h))

# sweep_rows_shape_nth: induction on the row index, peeling one row per
# step; the every-row hypothesis refines in lockstep (the head's is_eq is
# the and-left of the fold, the tail's fold is the and-right); the Nil
# cases are absurd through the bounds witness (an in-bounds index cannot
# point past the table).
def rows_shape_nth_go(i: Nat, rows: List<&2, List<&2, F32>>, +wp: Nat,
                      h: {S.rows_shape_ok(rows, wp) == True{} : Bool},
                      hi: R.lt_ok(i, S.rows_len(rows)))
  -> {Nat.is_eq(S.sweep_len(S.sweep_row(rows, i)), wp) == True{} : Bool}:
  match i rows h hi:
    case 0n r0 <> t hst _:
      PR.and_elim_l_go(Nat.is_eq(S.sweep_len(r0), wp), S.rows_shape_ok(t, wp), hst)
    case 0n Nil{} hst hlt:
      Empty.absurd({Nat.is_eq(S.sweep_len(S.sweep_row(Nil{}, 0n)), wp)
                    == True{} : Bool}, hlt)
    case 1n+p r0 <> +t hst hlt:
      rows_shape_nth_go(p, t, wp,
                        PR.and_elim_r_go(Nat.is_eq(S.sweep_len(r0), wp),
                                         S.rows_shape_ok(t, wp), hst), hlt)
    case 1n+p Nil{} hst hlt:
      Empty.absurd({Nat.is_eq(S.sweep_len(S.sweep_row(Nil{}, 1n+p)), wp)
                    == True{} : Bool}, hlt)

# h is needed twice (width and shape eliminations), so it is re-bound +
# (equality proofs are Data).
def Laws.sweep_rows_shape_nth(rows, wp, c, h, i, hi):
  +h2 = h
  hrest = PR.and_elim_r_go(Nat.is_le(S.rows_len(rows), 8n),
                           Bool.and(S.rows_shape_ok(rows, wp), R.ok(c)), h2)
  hshape = PR.and_elim_l_go(S.rows_shape_ok(rows, wp), R.ok(c), hrest)
  rows_shape_nth_go(i, rows, wp, hshape, hi)
