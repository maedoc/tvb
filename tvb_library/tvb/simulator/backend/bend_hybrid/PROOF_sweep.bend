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
import ./json_ingest.bend as J
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

# --------------------------------------------------------------------------
# the JSON SWEEP INGRESS
# --------------------------------------------------------------------------
# sw_cols_rows_len: induction on the builder's row counter k --
# rows_len(peel one row) == 1 + rows_len(rest), and the induction
# hypothesis equates the rest with p.
def cols_rows_len_go(+cols: List<&2, List<&2, F32>>, k: Nat, +i: Nat)
  -> {S.rows_len(S.cols_rows_go(cols, k, i)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z,
                 S.rows_len(S.cols_rows_go(cols, p, 1n+i)), p,
                 cols_rows_len_go(cols, p, 1n+i))

def Laws.sw_cols_rows_len(cols):
  cols_rows_len_go(cols, S.cols_ns(cols), 0n)

# the instances: pure computation on literal text / literal tables -- the
# tokenizer, the state machine, the 1e6 scaling and the validator all
# compute on concrete input.
def Laws.json_sweep_instance():
  {==}

def Laws.json_sweep_instance_shuffled():
  {==}

def Laws.json_sweep_garbage():
  {==}

def Laws.json_sweep_valid_instance():
  {==}

def Laws.json_sweep_valid_ragged():
  {==}

# the name->slot lookup: congruence under slot_of -- the k-th name IS the
# literal (the hypothesis), and slot_of computes on the literal name.
def Laws.sw_name_slot(names, k, h):
  Equal.trans(Nat,
    J.slot_of(S.str_nth(names, k)),
    J.slot_of("coupling_scale"),
    0n,
    Equal.cong(String, Nat, w => J.slot_of(w), S.str_nth(names, k), "coupling_scale", h),
    {==})

def Laws.sw_name_slot_unknown(names, k, h):
  Equal.trans(Nat,
    J.slot_of(S.str_nth(names, k)),
    J.slot_of("io_gain"),
    9n,
    Equal.cong(String, Nat, w => J.slot_of(w), S.str_nth(names, k), "io_gain", h),
    {==})

# THE CAPSTONE.  The validator hypothesis splits into the rows_ok half
# (the consistency conjunct rides unused -- the fan and the routing claims
# need only the width and the shared config's ok), the width conjunct
# converts to the decoded sim count through sw_cols_rows_len, and the
# three halves chain exactly like Laws.sweep_contract: col_to_row for the
# param half, fan8_exact for the result half, the PR.routing_contract_at
# bridge for the routing half.
def Laws.json_sweep_contract(s, c, runs, tk, i, j, h, hi, hj):
  +h2 = h
  +d = J.json_sweep_decode(s)
  +hrk = PR.and_elim_r_go(
          J.sw_consistent(J.sw_names(d), J.sw_cols(d)),
          S.sweep_rows_ok(S.cols_rows(J.sw_cols(d)), J.names_len(J.sw_names(d)), c),
          h2)
  hlenB = Laws.sweep_rows_ok_len(S.cols_rows(J.sw_cols(d)),
                                 J.names_len(J.sw_names(d)), c, hrk)
  c1 = Equal.cong(Nat, Bool, w => Nat.is_le(w, 8n),
                  S.rows_len(S.cols_rows(J.sw_cols(d))),
                  S.cols_ns(J.sw_cols(d)),
                  Laws.sw_cols_rows_len(J.sw_cols(d)))
  hnsB = Equal.trans(Bool,
           Nat.is_le(S.cols_ns(J.sw_cols(d)), 8n),
           Nat.is_le(S.rows_len(S.cols_rows(J.sw_cols(d))), 8n),
           True{},
           Equal.sym(Bool,
             Nat.is_le(S.rows_len(S.cols_rows(J.sw_cols(d))), 8n),
             Nat.is_le(S.cols_ns(J.sw_cols(d)), 8n), c1),
           hlenB)
  hw = PR.b_le(S.cols_ns(J.sw_cols(d)), 8n, hnsB)
  hok = Laws.sweep_rows_ok_cfg(S.cols_rows(J.sw_cols(d)),
                               J.names_len(J.sw_names(d)), c, hrk)
  hcol = Laws.col_to_row(J.sw_cols(d), i, j)
  hfan = Laws.fan8_exact(runs, S.cols_ns(J.sw_cols(d)), i, hw, hi)
  hrun = PR.routing_contract_at(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c),
                                tk, j, hok, {==}, {==}, hj)
  Equal.trans(F32 & (String & Bool),
    (S.sweep_nth(S.col_row(J.sw_cols(d), i), j),
     S.str_nth(S.fan8(S.cols_ns(J.sw_cols(d)), runs), i),
     S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
    (S.sweep_nth(S.col_nth(J.sw_cols(d), j), i),
     S.str_nth(S.fan8(S.cols_ns(J.sw_cols(d)), runs), i),
     S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
    (S.sweep_nth(S.col_nth(J.sw_cols(d), j), i), S.str_nth(runs, i), True{}),
    Equal.cong(F32, F32 & (String & Bool),
               w => (w,
                     S.str_nth(S.fan8(S.cols_ns(J.sw_cols(d)), runs), i),
                     S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
               S.sweep_nth(S.col_row(J.sw_cols(d), i), j),
               S.sweep_nth(S.col_nth(J.sw_cols(d), j), i), hcol),
    Equal.trans(F32 & (String & Bool),
      (S.sweep_nth(S.col_nth(J.sw_cols(d), j), i),
       S.str_nth(S.fan8(S.cols_ns(J.sw_cols(d)), runs), i),
       S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
      (S.sweep_nth(S.col_nth(J.sw_cols(d), j), i), S.str_nth(runs, i),
       S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
      (S.sweep_nth(S.col_nth(J.sw_cols(d), j), i), S.str_nth(runs, i), True{}),
      Equal.cong(String, F32 & (String & Bool),
                 w => (S.sweep_nth(S.col_nth(J.sw_cols(d), j), i), w,
                       S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j)),
                 S.str_nth(S.fan8(S.cols_ns(J.sw_cols(d)), runs), i),
                 S.str_nth(runs, i), hfan),
      Equal.cong(Bool, F32 & (String & Bool),
                 w => (S.sweep_nth(S.col_nth(J.sw_cols(d), j), i),
                       S.str_nth(runs, i), w),
                 S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), tk, j),
                 True{}, hrun)))

# --------------------------------------------------------------------------
# P2 -- the CONNECTOME SWEEP (per-sim CSR payloads over a shared shape)
# --------------------------------------------------------------------------
# sweep_csr_route: the sweep_row_nth induction at the payload level --
# peel one payload record per step; the witness refines with the peel;
# the Nil cases are absurd through the witness.

def pay_nth_route_go(i: Nat, pays: List<&2, S.CsrPay>,
                     h: R.lt_ok(i, S.pays_len(pays)))
  -> {S.pay_nth(pays, i) == S.pay_ref(pays, i) : S.CsrPay}:
  match i pays h:
    case 0n Nil{} hlt:
      Empty.absurd({S.pay_nth(Nil{}, 0n) == S.pay_ref(Nil{}, 0n) : S.CsrPay}, hlt)
    case 0n p0 <> t _:
      {==}
    case 1n+p Nil{} hlt:
      Empty.absurd({S.pay_nth(Nil{}, 1n+p) == S.pay_ref(Nil{}, 1n+p) : S.CsrPay}, hlt)
    case 1n+p p0 <> t hlt:
      pay_nth_route_go(p, t, hlt)

def Laws.sweep_csr_route(pays, i, h):
  pay_nth_route_go(i, pays, h)

# the instance pins: pure computation on the literal payload table.
def Laws.sweep_csr_route_inst_0():
  {==}

def Laws.sweep_csr_route_inst_1():
  {==}

# sweep_csr_shape_shared: the rows_shape_nth induction at the payload
# level -- peel one payload per step; the every-row hypothesis refines
# in lockstep (the head's pay_shape_ok is the and-left of the fold, the
# tail's fold is the and-right); the Nil cases are absurd through the
# bounds witness.
def cs_shape_nth_go(i: Nat, pays: List<&2, S.CsrPay>, +n: Nat,
                    h: {S.cs_shape_ok(pays, n) == True{} : Bool},
                    hi: R.lt_ok(i, S.pays_len(pays)))
  -> {S.pay_shape_ok(S.pay_nth(pays, i), n) == True{} : Bool}:
  match i pays h hi:
    case 0n p0 <> t hst _:
      PR.and_elim_l_go(S.pay_shape_ok(p0, n), S.cs_shape_ok(t, n), hst)
    case 0n Nil{} hst hlt:
      Empty.absurd({S.pay_shape_ok(S.pay_nth(Nil{}, 0n), n) == True{} : Bool}, hlt)
    case 1n+p p0 <> +t hst hlt:
      cs_shape_nth_go(p, t, n,
                      PR.and_elim_r_go(S.pay_shape_ok(p0, n),
                                       S.cs_shape_ok(t, n), hst), hlt)
    case 1n+p Nil{} hst hlt:
      Empty.absurd({S.pay_shape_ok(S.pay_nth(Nil{}, 1n+p), n) == True{} : Bool}, hlt)

def Laws.sweep_csr_shape_shared(pays, ixs, h, i, hi):
  cs_shape_nth_go(i, pays, R.nats_len(ixs), h, hi)

# sweep_csr_valid_nth: the same induction over the PER-ROW csr_ok fold --
# the head's R.csr_ok is the and-left, the tail's fold the and-right.
def cs_valid_nth_go(i: Nat, pays: List<&2, S.CsrPay>,
                    +nsrc: Nat, +horizon: Nat,
                    +indptr: List<&2, Nat>, +ixs: List<&2, Nat>,
                    h: {S.cs_rows_csr_ok(nsrc, horizon, indptr, ixs, pays)
                          == True{} : Bool},
                    hi: R.lt_ok(i, S.pays_len(pays)))
  -> {R.csr_ok(nsrc, horizon, S.pay_csr(indptr, ixs, S.pay_nth(pays, i)))
        == True{} : Bool}:
  match i pays h hi:
    case 0n p0 <> t hst _:
      PR.and_elim_l_go(R.csr_ok(nsrc, horizon, S.pay_csr(indptr, ixs, p0)),
                       S.cs_rows_csr_ok(nsrc, horizon, indptr, ixs, t), hst)
    case 0n Nil{} hst hlt:
      Empty.absurd({R.csr_ok(nsrc, horizon,
                             S.pay_csr(indptr, ixs, S.pay_nth(Nil{}, 0n)))
                      == True{} : Bool}, hlt)
    case 1n+p p0 <> +t hst hlt:
      cs_valid_nth_go(p, t, nsrc, horizon, indptr, ixs,
                      PR.and_elim_r_go(R.csr_ok(nsrc, horizon,
                                                S.pay_csr(indptr, ixs, p0)),
                                       S.cs_rows_csr_ok(nsrc, horizon, indptr,
                                                        ixs, t), hst), hlt)
    case 1n+p Nil{} hst hlt:
      Empty.absurd({R.csr_ok(nsrc, horizon,
                             S.pay_csr(indptr, ixs, S.pay_nth(Nil{}, 1n+p)))
                      == True{} : Bool}, hlt)

# the fill: strip the width / shape conjuncts off the four-deep validator
# and, then the fold induction at the derived (nsrc, horizon).
def Laws.sweep_csr_valid_nth(indptr, ixs, pays, c, h, i, hi):
  +h2 = h
  hX = PR.and_elim_r_go(Nat.is_le(S.pays_len(pays), 8n),
                        Bool.and(S.cs_shape_ok(pays, R.nats_len(ixs)),
                                 Bool.and(S.cs_rows_csr_ok(
                                            R.nats_len(R.cfg_lanes(c)),
                                            R.cfg_horizon(c), indptr, ixs, pays),
                                          R.ok(c))),
                        h2)
  hY = PR.and_elim_r_go(S.cs_shape_ok(pays, R.nats_len(ixs)),
                        Bool.and(S.cs_rows_csr_ok(R.nats_len(R.cfg_lanes(c)),
                                                  R.cfg_horizon(c), indptr,
                                                  ixs, pays),
                                 R.ok(c)),
                        hX)
  hCR = PR.and_elim_l_go(S.cs_rows_csr_ok(R.nats_len(R.cfg_lanes(c)),
                                          R.cfg_horizon(c), indptr, ixs, pays),
                         R.ok(c), hY)
  cs_valid_nth_go(i, pays, R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
                  indptr, ixs, hCR, hi)

# the and-elimination family: width, shape, csr_ok-fold, shared-config ok,
# each peeling one layer off the nested and (the sweep_rows_ok pattern).
def Laws.sweep_csr_ok_width(indptr, ixs, pays, c, h):
  PR.and_elim_l_go(Nat.is_le(S.pays_len(pays), 8n),
                   Bool.and(S.cs_shape_ok(pays, R.nats_len(ixs)),
                            Bool.and(S.cs_rows_csr_ok(R.nats_len(R.cfg_lanes(c)),
                                                      R.cfg_horizon(c),
                                                      indptr, ixs, pays),
                                     R.ok(c))),
                   h)

def Laws.sweep_csr_ok_shape(indptr, ixs, pays, c, h):
  PR.and_elim_l_go(S.cs_shape_ok(pays, R.nats_len(ixs)),
                   Bool.and(S.cs_rows_csr_ok(R.nats_len(R.cfg_lanes(c)),
                                             R.cfg_horizon(c), indptr, ixs,
                                             pays),
                            R.ok(c)),
                   PR.and_elim_r_go(Nat.is_le(S.pays_len(pays), 8n),
                                    Bool.and(S.cs_shape_ok(pays,
                                                           R.nats_len(ixs)),
                                             Bool.and(S.cs_rows_csr_ok(
                                                        R.nats_len(R.cfg_lanes(c)),
                                                        R.cfg_horizon(c),
                                                        indptr, ixs, pays),
                                                      R.ok(c))),
                                    h))

def Laws.sweep_csr_ok_csr(indptr, ixs, pays, c, h):
  PR.and_elim_l_go(S.cs_rows_csr_ok(R.nats_len(R.cfg_lanes(c)),
                                    R.cfg_horizon(c), indptr, ixs, pays),
                   R.ok(c),
                   PR.and_elim_r_go(S.cs_shape_ok(pays, R.nats_len(ixs)),
                                    Bool.and(S.cs_rows_csr_ok(
                                               R.nats_len(R.cfg_lanes(c)),
                                               R.cfg_horizon(c), indptr, ixs,
                                               pays),
                                             R.ok(c)),
                                    PR.and_elim_r_go(Nat.is_le(S.pays_len(pays), 8n),
                                                     Bool.and(S.cs_shape_ok(
                                                                pays,
                                                                R.nats_len(ixs)),
                                                              Bool.and(S.cs_rows_csr_ok(
                                                                         R.nats_len(R.cfg_lanes(c)),
                                                                         R.cfg_horizon(c),
                                                                         indptr, ixs, pays),
                                                                       R.ok(c))),
                                                     h)))

def Laws.sweep_csr_ok_cfg(indptr, ixs, pays, c, h):
  PR.and_elim_r_go(S.cs_rows_csr_ok(R.nats_len(R.cfg_lanes(c)),
                                    R.cfg_horizon(c), indptr, ixs, pays),
                   R.ok(c),
                   PR.and_elim_r_go(S.cs_shape_ok(pays, R.nats_len(ixs)),
                                    Bool.and(S.cs_rows_csr_ok(
                                               R.nats_len(R.cfg_lanes(c)),
                                               R.cfg_horizon(c), indptr, ixs,
                                               pays),
                                             R.ok(c)),
                                    PR.and_elim_r_go(Nat.is_le(S.pays_len(pays), 8n),
                                                     Bool.and(S.cs_shape_ok(
                                                                pays,
                                                                R.nats_len(ixs)),
                                                              Bool.and(S.cs_rows_csr_ok(
                                                                         R.nats_len(R.cfg_lanes(c)),
                                                                         R.cfg_horizon(c),
                                                                         indptr, ixs, pays),
                                                                       R.ok(c))),
                                                     h)))

# the positive validator pin: pure computation on the literal sweep and
# the literal config -- every conjunct computes on concrete input.
def Laws.sweep_csr_ok_instance():
  {==}

# the capstone: three cong steps under Equal.trans -- one per component
# of the right-nested triple -- with the routing half from
# Laws.sweep_csr_valid_nth, the routing-half's read keyed to the ROUTED
# payload (pay_nth), exactly the form the composition needs.
def Laws.sweep_csr_contract(indptr, ixs, pays, c, h, i, hi):
  +h2 = h
  +hiB = sw_le_b(Nat.add(i, 1n), S.pays_len(pays), hi)
  hroute = Laws.sweep_csr_route(pays, i,
                                PR.b_le(Nat.add(i, 1n), S.pays_len(pays), hiB))
  hvalid = Laws.sweep_csr_valid_nth(indptr, ixs, pays, c, h2, i,
                                    PR.b_le(Nat.add(i, 1n), S.pays_len(pays), hiB))
  hshape = Laws.sweep_csr_shape_shared(pays, ixs,
                                       Laws.sweep_csr_ok_shape(indptr, ixs,
                                                               pays, c, h2),
                                       i,
                                       PR.b_le(Nat.add(i, 1n), S.pays_len(pays), hiB))
  Equal.trans(S.CsrPay & (Bool & Bool),
    (S.pay_nth(pays, i),
     R.csr_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
              S.pay_csr(indptr, ixs, S.pay_nth(pays, i))),
     S.pay_shape_ok(S.pay_nth(pays, i), R.nats_len(ixs))),
    (S.pay_ref(pays, i),
     R.csr_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
              S.pay_csr(indptr, ixs, S.pay_nth(pays, i))),
     S.pay_shape_ok(S.pay_nth(pays, i), R.nats_len(ixs))),
    (S.pay_ref(pays, i), True{}, True{}),
    Equal.cong(S.CsrPay, S.CsrPay & (Bool & Bool),
               w => (w,
                     R.csr_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
                              S.pay_csr(indptr, ixs, S.pay_nth(pays, i))),
                     S.pay_shape_ok(S.pay_nth(pays, i), R.nats_len(ixs))),
               S.pay_nth(pays, i), S.pay_ref(pays, i), hroute),
    Equal.trans(S.CsrPay & (Bool & Bool),
      (S.pay_ref(pays, i),
       R.csr_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
                S.pay_csr(indptr, ixs, S.pay_nth(pays, i))),
       S.pay_shape_ok(S.pay_nth(pays, i), R.nats_len(ixs))),
      (S.pay_ref(pays, i), True{},
       S.pay_shape_ok(S.pay_nth(pays, i), R.nats_len(ixs))),
      (S.pay_ref(pays, i), True{}, True{}),
      Equal.cong(Bool, S.CsrPay & (Bool & Bool),
                 w => (S.pay_ref(pays, i), w,
                       S.pay_shape_ok(S.pay_nth(pays, i), R.nats_len(ixs))),
                 R.csr_ok(R.nats_len(R.cfg_lanes(c)), R.cfg_horizon(c),
                          S.pay_csr(indptr, ixs, S.pay_nth(pays, i))),
                 True{}, hvalid),
      Equal.cong(Bool, S.CsrPay & (Bool & Bool),
                 w => (S.pay_ref(pays, i), True{}, w),
                 S.pay_shape_ok(S.pay_nth(pays, i), R.nats_len(ixs)),
                 True{}, hshape)))

# --------------------------------------------------------------------------
# P3b -- the STOCHASTIC SEEDS: proofs
# --------------------------------------------------------------------------
# Two arithmetic bricks first.  Laws.add_zero / Laws.add_succ exist as
# PROOF_router law FILLS, which do not re-export across module imports
# (the NOTES rule), so their go-lemmas are copied here -- the sw_le_b
# precedent.
def add_zero_l(x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, add_zero_l(p))

def add_succ_r(a: Nat, b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z,
                 Nat.add(p, 1n+b), Nat.add(1n+p, b),
                 add_succ_r(p, b))

# the instance pins: pure computation on the literal seed column.
def Laws.seed_nth_head(h, t):
  {==}

def Laws.seed_nth_step(h, t, k):
  {==}

# seed_route: the sweep_nth_route induction over a Nat column -- peel one
# element per step; the witness refines with the peel; the Nil cases are
# absurd through the witness.
def seed_nth_route_go(k: Nat, xs: List<&2, Nat>, h: R.lt_ok(k, R.nats_len(xs)))
  -> {S.seed_nth(xs, k) == S.seed_ref(xs, k) : Nat}:
  match k xs h:
    case 0n Nil{} hlt:
      Empty.absurd({S.seed_nth(Nil{}, 0n) == S.seed_ref(Nil{}, 0n) : Nat}, hlt)
    case 0n h0 <> t _:
      {==}
    case 1n+p Nil{} hlt:
      Empty.absurd({S.seed_nth(Nil{}, 1n+p) == S.seed_ref(Nil{}, 1n+p) : Nat}, hlt)
    case 1n+p h0 <> t hlt:
      seed_nth_route_go(p, t, hlt)

def Laws.seed_route(xs, k, h):
  seed_nth_route_go(k, xs, h)

def Laws.seed_route_inst_0():
  {==}

def Laws.seed_route_inst_1():
  {==}

def Laws.seed_route_inst_2():
  {==}

# seed_row_nth: induction with the row counter k shrinking and the sim
# index i peeled in lockstep; the running index j rides (the go concludes
# the j-generalized form add(base, add(j, i)), of which the law's
# add(base, i) is the j = 0n instance -- Nat.add(0n, i) reduces to i).
# The base case bridges Nat.add(j, 0n) to j with add_zero_l; the step
# bridges Nat.add(j, 1n+p) to 1n+Nat.add(j, p) with add_succ_r -- the two
# stuck-Nat.add normal forms the counted loop produces.
def seed_row_nth_go(+base: Nat, k: Nat, +j: Nat, i: Nat, h: R.lt_ok(i, k))
  -> {S.seed_nth(S.seed_row_go(base, k, j), i)
        == Nat.add(base, Nat.add(j, i)) : Nat}:
  match k i h:
    case 0n _ hlt:
      Empty.absurd({S.seed_nth(S.seed_row_go(base, 0n, j), i)
                      == Nat.add(base, Nat.add(j, i)) : Nat},
                   lt_zero_absurd(i, hlt))
    case 1n+m 0n _:
      Equal.sym(Nat,
        Nat.add(base, Nat.add(j, 0n)),
        Nat.add(base, j),
        Equal.cong(Nat, Nat, x => Nat.add(base, x),
                   Nat.add(j, 0n), j, add_zero_l(j)))
    case 1n+(+m) 1n+(+p) hlt:
      Equal.trans(Nat,
        S.seed_nth(S.seed_row_go(base, 1n+m, j), 1n+p),
        Nat.add(base, 1n+Nat.add(j, p)),
        Nat.add(base, Nat.add(j, 1n+p)),
        seed_row_nth_go(base, m, 1n+j, p, hlt),
        Equal.sym(Nat,
          Nat.add(base, Nat.add(j, 1n+p)),
          Nat.add(base, 1n+Nat.add(j, p)),
          Equal.cong(Nat, Nat, x => Nat.add(base, x),
                     Nat.add(j, 1n+p), 1n+Nat.add(j, p),
                     add_succ_r(j, p))))

def Laws.seed_row_nth(base, n, i, h):
  seed_row_nth_go(base, n, 0n, i, h)

# seed_distinct: induction on the increment base.  At base = 0n both
# sides reduce to i and j and the claim IS lt_imp_ne; at base = 1n+b both
# sides peel one successor in lockstep (Nat.add recurses on its FIRST
# argument, so Nat.add(1n+b, x) reduces to 1n+Nat.add(b, x) and is_ne
# peels with it).  The lt hypothesis rides along -- Bool proofs are Data.
def seed_distinct_go(+base: Nat, +i: Nat, +j: Nat,
                     h: {Nat.is_lt(i, j) == True{} : Bool})
  -> {Nat.is_ne(Nat.add(base, i), Nat.add(base, j)) == True{} : Bool}:
  match base:
    case 0n:
      PR.lt_imp_ne(i, j, h)
    case 1n+b:
      seed_distinct_go(b, i, j, h)

def Laws.seed_distinct(base, i, j, h):
  seed_distinct_go(base, i, j, h)

# seed_deterministic: the routing read applied twice -- a rerun -- lands
# on the same reference element both times (seed_route instantiated
# twice; the index witness is carried in Bool form and rebuilt per use,
# the mc_contract idiom).
def Laws.seed_deterministic(seeds, i, hib):
  +hib2 = hib
  e1 = Laws.seed_route(seeds, i,
                       PR.b_le(Nat.add(i, 1n), R.nats_len(seeds), hib))
  e2 = Laws.seed_route(seeds, i,
                       PR.b_le(Nat.add(i, 1n), R.nats_len(seeds), hib2))
  Equal.trans(Nat & Nat,
    (S.seed_nth(seeds, i), S.seed_nth(seeds, i)),
    (S.seed_ref(seeds, i), S.seed_nth(seeds, i)),
    (S.seed_ref(seeds, i), S.seed_ref(seeds, i)),
    Equal.cong(Nat, Nat & Nat, w => (w, S.seed_nth(seeds, i)),
               S.seed_nth(seeds, i), S.seed_ref(seeds, i), e1),
    Equal.cong(Nat, Nat & Nat, w => (S.seed_ref(seeds, i), w),
               S.seed_nth(seeds, i), S.seed_ref(seeds, i), e2))

# the validator's and-elimination family (the sweep_rows_ok pattern):
# width /\ (distinct /\ R.ok), each half eliminating down the spine.
def Laws.sweep_seed_ok_width(seeds, c, h):
  PR.and_elim_l_go(Nat.is_le(R.nats_len(seeds), 8n),
                   Bool.and(S.seeds_unique(seeds), R.ok(c)), h)

def Laws.sweep_seed_ok_distinct(seeds, c, h):
  PR.and_elim_l_go(S.seeds_unique(seeds), R.ok(c),
                   PR.and_elim_r_go(Nat.is_le(R.nats_len(seeds), 8n),
                                    Bool.and(S.seeds_unique(seeds), R.ok(c)),
                                    h))

def Laws.sweep_seed_ok_cfg(seeds, c, h):
  PR.and_elim_r_go(S.seeds_unique(seeds), R.ok(c),
                   PR.and_elim_r_go(Nat.is_le(R.nats_len(seeds), 8n),
                                    Bool.and(S.seeds_unique(seeds), R.ok(c)),
                                    h))

# the instance pins: pure computation on the literal column and config.
def Laws.sweep_seed_ok_instance():
  {==}

def Laws.seeds_unique_dup():
  {==}

# the per-index distinctness: the ok_no_clash induction over the seed
# column.  The head lemma peels the clash fold (the head's is_ne is the
# and-left, the tail's fold the and-right); the pairwise go peels both
# indices in lockstep, with the equal-index case refuted through the
# strict-order hypothesis (ia < ib forbids ia == ib).
def no_clash_nth_go(+s: Nat, ts: List<&2, Nat>, +q: Nat,
                    hq: R.lt_ok(q, R.nats_len(ts)),
                    hu: {S.no_seed_clash(s, ts) == True{} : Bool})
  -> {Nat.is_ne(s, R.nats_nth(ts, q)) == True{} : Bool}:
  match ts q hq:
    case Nil{} _ hlt:
      Empty.absurd({Nat.is_ne(s, R.nats_nth(Nil{}, q)) == True{} : Bool},
                   PR.lt_ok_nil_absurd(q, hlt))
    case h0 <> +t 0n _:
      PR.and_elim_l_go(Nat.is_ne(s, h0), S.no_seed_clash(s, t), hu)
    case h0 <> +t 1n+p hlt:
      no_clash_nth_go(s, t, p, hlt,
                      PR.and_elim_r_go(Nat.is_ne(s, h0),
                                       S.no_seed_clash(s, t), hu))

def seeds_distinct_go(seeds: List<&2, Nat>, ia: Nat, ib: Nat,
                      hltb: {Nat.is_lt(ia, ib) == True{} : Bool},
                      ha: R.lt_ok(ia, R.nats_len(seeds)),
                      hb: R.lt_ok(ib, R.nats_len(seeds)),
                      hu: {S.seeds_unique(seeds) == True{} : Bool})
  -> {Nat.is_ne(R.nats_nth(seeds, ia), R.nats_nth(seeds, ib)) == True{} : Bool}:
  match seeds ia ha:
    case Nil{} _ h:
      Empty.absurd({Nat.is_ne(R.nats_nth(Nil{}, ia), R.nats_nth(Nil{}, ib))
                      == True{} : Bool},
                   PR.lt_ok_nil_absurd(ia, h))
    case +s0 <> +t 0n _:
      match ib:
        case 0n:
          Bool.fne({Nat.is_ne(R.nats_nth(s0 <> t, 0n),
                              R.nats_nth(s0 <> t, 0n)) == True{} : Bool},
                   Bool.fne({Nat.is_lt(0n, 0n) == True{} : Bool}, hltb))
        case 1n+q:
          no_clash_nth_go(s0, t, q, hb,
                          PR.and_elim_l_go(S.no_seed_clash(s0, t),
                                           S.seeds_unique(t), hu))
    case +s0 <> +t 1n+q hlt:
      match ib:
        case 0n:
          Bool.fne({Nat.is_ne(R.nats_nth(s0 <> t, 1n+q),
                              R.nats_nth(s0 <> t, 0n)) == True{} : Bool},
                   Bool.fne({Nat.is_lt(1n+q, 0n) == True{} : Bool}, hltb))
        case 1n+r:
          seeds_distinct_go(t, q, r, hltb, hlt, hb,
                            PR.and_elim_r_go(S.no_seed_clash(s0, t),
                                             S.seeds_unique(t), hu))

def Laws.seeds_distinct_nth(seeds, ia, ib, hltb, ha, hb, hu):
  seeds_distinct_go(seeds, ia, ib, hltb, ha, hb, hu)

# THE CAPSTONE.  Three cong steps under Equal.trans -- one per component
# of the right-nested triple: the param half from Laws.sweep_nth_route,
# the seed half from Laws.seed_route, the fan half from Laws.fan8_exact
# with the width witness DERIVED from the parameter validator
# (sweep_ok_width).  The index witnesses ride in Bool form and are
# rebuilt per use (the mc_contract idiom -- the param read and the fan
# BOTH need the table's index witness).
def Laws.sweep_seeded_contract(t, seeds, c, runs, i, h, hs, hkB, hsB):
  hwB = Laws.sweep_ok_width(t, c, h)
  hw = PR.b_le(S.sweep_len(t), 8n, hwB)
  hparam = Laws.sweep_nth_route(t, i,
                                PR.b_le(Nat.add(i, 1n), S.sweep_len(t), hkB))
  hseed = Laws.seed_route(seeds, i,
                          PR.b_le(Nat.add(i, 1n), R.nats_len(seeds), hsB))
  hfan = Laws.fan8_exact(runs, S.sweep_len(t), i, hw,
                         PR.b_le(Nat.add(i, 1n), S.sweep_len(t), hkB))
  Equal.trans(F32 & (Nat & String),
    (S.sweep_nth(t, i), S.seed_nth(seeds, i),
     S.str_nth(S.fan8(S.sweep_len(t), runs), i)),
    (S.sweep_word(t, i), S.seed_nth(seeds, i),
     S.str_nth(S.fan8(S.sweep_len(t), runs), i)),
    (S.sweep_word(t, i), S.seed_ref(seeds, i), S.str_nth(runs, i)),
    Equal.cong(F32, F32 & (Nat & String),
               w => (w, S.seed_nth(seeds, i),
                     S.str_nth(S.fan8(S.sweep_len(t), runs), i)),
               S.sweep_nth(t, i), S.sweep_word(t, i), hparam),
    Equal.trans(F32 & (Nat & String),
      (S.sweep_word(t, i), S.seed_nth(seeds, i),
       S.str_nth(S.fan8(S.sweep_len(t), runs), i)),
      (S.sweep_word(t, i), S.seed_ref(seeds, i),
       S.str_nth(S.fan8(S.sweep_len(t), runs), i)),
      (S.sweep_word(t, i), S.seed_ref(seeds, i), S.str_nth(runs, i)),
      Equal.cong(Nat, F32 & (Nat & String),
                 w => (S.sweep_word(t, i), w,
                       S.str_nth(S.fan8(S.sweep_len(t), runs), i)),
                 S.seed_nth(seeds, i), S.seed_ref(seeds, i), hseed),
      Equal.cong(String, F32 & (Nat & String),
                 w => (S.sweep_word(t, i), S.seed_ref(seeds, i), w),
                 S.str_nth(S.fan8(S.sweep_len(t), runs), i),
                 S.str_nth(runs, i), hfan)))

# --------------------------------------------------------------------------
# P5 -- the OUTPUT UN-ROUTING: proofs
# --------------------------------------------------------------------------
# out_block route half: the sweep_row_nth induction at the block level --
# peel one block per step; the witness refines with the peel; the Nil
# cases are absurd through the witness.

def out_block_nth_go(i: Nat, outs: List<&2, List<&2, List<&2, F32>>>,
                     h: R.lt_ok(i, S.outs_len(outs)))
  -> {S.out_block(outs, i) == S.out_block_ref(outs, i) : List<&2, List<&2, F32>>}:
  match i outs h:
    case 0n Nil{} hlt:
      Empty.absurd({S.out_block(Nil{}, 0n) == S.out_block_ref(Nil{}, 0n)
                    : List<&2, List<&2, F32>>}, hlt)
    case 0n o0 <> t _:
      {==}
    case 1n+p Nil{} hlt:
      Empty.absurd({S.out_block(Nil{}, 1n+p) == S.out_block_ref(Nil{}, 1n+p)
                    : List<&2, List<&2, F32>>}, hlt)
    case 1n+p o0 <> t hlt:
      out_block_nth_go(p, t, hlt)

def Laws.out_route(outs, i, s, hi, hs):
  hblk = out_block_nth_go(i, outs, hi)
  hrow = Laws.sweep_row_nth(S.out_block(outs, i), s, hs)
  h2 = Equal.cong((List<&2, List<&2, F32>>), List<&2, F32>,
                  w => S.sweep_row_ref(w, s),
                  S.out_block(outs, i), S.out_block_ref(outs, i), hblk)
  Equal.trans(List<&2, F32>,
    S.out_slice(outs, i, s),
    S.sweep_row_ref(S.out_block(outs, i), s),
    S.out_slice_ref(outs, i, s),
    hrow, h2)

# out_block_route: the fan8_exact induction at the output plane -- peel
# one lane of out_fan_go per step.  Two witnesses: lt_ok(i, a) -- the lane
# is active (an inactive lane contributes NO block, so a phantom Nil would
# clash); le_ok(a, w) -- the WIDTH witness, load-bearing at w = 0 with
# a > 0 (dropped lanes).  Blocks may stay symbolic in the a = 0 arms and
# the i = 0 active arm: the fan cell reduces without looking past the
# block table's head.
def out_block_route_go(w: Nat, a: Nat,
                       blocks: List<&2, List<&2, List<&2, F32>>>, i: Nat,
                       hw: R.le_ok(a, w), h: R.lt_ok(i, a))
  -> {S.out_block(S.out_fan_go(w, a, blocks), i) == S.out_block(blocks, i)
      : List<&2, List<&2, F32>>}:
  match w a blocks i hw h:
    case 0n 0n blks _ _ hlt:
      Empty.absurd({S.out_block(S.out_fan_go(0n, 0n, blks), i)
                      == S.out_block(blks, i) : List<&2, List<&2, F32>>},
                   lt_zero_absurd(i, hlt))
    case 0n 1n+d blks _ hw _:
      Empty.absurd({S.out_block(S.out_fan_go(0n, 1n+d, blks), i)
                      == S.out_block(blks, i) : List<&2, List<&2, F32>>}, hw)
    case 1n+s 0n blks 0n _ hlt:
      Empty.absurd({S.out_block(S.out_fan_go(1n+s, 0n, blks), 0n)
                      == S.out_block(blks, 0n) : List<&2, List<&2, F32>>}, hlt)
    case 1n+s 0n blks 1n+p _ hlt:
      Empty.absurd({S.out_block(S.out_fan_go(1n+s, 0n, blks), 1n+p)
                      == S.out_block(blks, 1n+p) : List<&2, List<&2, F32>>}, hlt)
    case 1n+s 1n+d rns 0n _ _:
      {==}
    case 1n+s 1n+d r0 <> t 1n+p hw hlt:
      out_block_route_go(s, d, t, p, hw, hlt)
    case 1n+s 1n+d Nil{} 1n+p hw hlt:
      out_block_route_go(s, d, Nil{}, p, hw, hlt)

def Laws.out_block_route(blocks, n, i, hw, h):
  out_block_route_go(8n, n, blocks, i, hw, h)

# out_fan_len: induction on (w, a) in lockstep.  The width witness is
# load-bearing at w = 0 with a > 0 (dropped lanes: the output has 0
# blocks, not a); the a = 0 arm goes through the all-inactive lemma (the
# fan contributes nothing, so the count is 0); the step counts the head
# block and the induction hypothesis.
def out_fan_zero_len_go(w: Nat, blocks: List<&2, List<&2, List<&2, F32>>>)
  -> {S.outs_len(S.out_fan_go(w, 0n, blocks)) == 0n : Nat}:
  match w:
    case 0n:
      {==}
    case 1n+s:
      out_fan_zero_len_go(s, S.outs_tail(blocks))

def out_fan_len_go(w: Nat, a: Nat,
                   blocks: List<&2, List<&2, List<&2, F32>>>,
                   hw: R.le_ok(a, w))
  -> {S.outs_len(S.out_fan_go(w, a, blocks)) == a : Nat}:
  match w a blocks hw:
    case 0n 0n _ _:
      {==}
    case 0n 1n+d _ hw:
      Empty.absurd({S.outs_len(S.out_fan_go(0n, 1n+d, Nil{})) == 1n+d : Nat}, hw)
    case 1n+s 0n blks _:
      out_fan_zero_len_go(s, S.outs_tail(blks))
    case 1n+s 1n+d r0 <> t hw:
      Equal.cong(Nat, Nat, z => 1n+z,
                 S.outs_len(S.out_fan_go(s, d, t)), d,
                 out_fan_len_go(s, d, t, hw))
    case 1n+s 1n+d Nil{} hw:
      Equal.cong(Nat, Nat, z => 1n+z,
                 S.outs_len(S.out_fan_go(s, d, Nil{})), d,
                 out_fan_len_go(s, d, Nil{}, hw))

def Laws.out_fan_len(blocks, n, hw):
  out_fan_len_go(8n, n, blocks, hw)

# out_block_len: induction on the subnet count -- the builder conses one
# series per count step, so the length counts in lockstep.
def block_len_go(+n: Nat, +series: List<&2, List<&2, F32>>)
  -> {S.rows_len(S.block_go(n, series)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z,
                 S.rows_len(S.block_go(p, S.rows_drop(series, 1n))), p,
                 block_len_go(p, S.rows_drop(series, 1n)))

def Laws.out_block_len(n, series):
  block_len_go(n, series)

# the instance pins: pure computation on the literal 2x2 output table.
def Laws.out_slice_inst_0_0():
  {==}

def Laws.out_slice_inst_0_1():
  {==}

def Laws.out_slice_inst_1_0():
  {==}

def Laws.out_slice_inst_1_1():
  {==}

# the output capstone: two cong steps under Equal.trans -- the block half
# from Laws.out_block_route (width witness DERIVED from the sweep
# validator, sweep_ok_width), the cell half the same route lifted through
# the proved series read (sweep_row).  The first trans leg is the
# definitional unfold of out_slice into block-read + series-read.
def Laws.sweep_out_contract(t, blocks, c, i, s, h, hi):
  hwB = Laws.sweep_ok_width(t, c, h)
  hw = PR.b_le(S.sweep_len(t), 8n, hwB)
  +hblk = Laws.out_block_route(blocks, S.sweep_len(t), i, hw, hi)
  hcell = Equal.cong((List<&2, List<&2, F32>>), List<&2, F32>,
                     w => S.sweep_row(w, s),
                     S.out_block(S.out_fan(S.sweep_len(t), blocks), i),
                     S.out_block(blocks, i), hblk)
  hAB = Equal.trans(List<&2, F32> & List<&2, List<&2, F32>>,
    (S.out_slice(S.out_fan(S.sweep_len(t), blocks), i, s),
     S.out_block(S.out_fan(S.sweep_len(t), blocks), i)),
    (S.sweep_row(S.out_block(S.out_fan(S.sweep_len(t), blocks), i), s),
     S.out_block(S.out_fan(S.sweep_len(t), blocks), i)),
    (S.sweep_row(S.out_block(blocks, i), s),
     S.out_block(S.out_fan(S.sweep_len(t), blocks), i)),
    {==},
    Equal.cong((List<&2, F32>),
               (List<&2, F32> & (List<&2, List<&2, F32>>)),
               w => (w, S.out_block(S.out_fan(S.sweep_len(t), blocks), i)),
               S.sweep_row(S.out_block(S.out_fan(S.sweep_len(t), blocks), i), s),
               S.sweep_row(S.out_block(blocks, i), s), hcell))
  Equal.trans(List<&2, F32> & List<&2, List<&2, F32>>,
    (S.out_slice(S.out_fan(S.sweep_len(t), blocks), i, s),
     S.out_block(S.out_fan(S.sweep_len(t), blocks), i)),
    (S.sweep_row(S.out_block(blocks, i), s),
     S.out_block(S.out_fan(S.sweep_len(t), blocks), i)),
    (S.sweep_row(S.out_block(blocks, i), s), S.out_block(blocks, i)),
    hAB,
    Equal.cong((List<&2, List<&2, F32>>),
               (List<&2, F32> & (List<&2, List<&2, F32>>)),
               w => (S.sweep_row(S.out_block(blocks, i), s), w),
               S.out_block(S.out_fan(S.sweep_len(t), blocks), i),
               S.out_block(blocks, i), hblk))
