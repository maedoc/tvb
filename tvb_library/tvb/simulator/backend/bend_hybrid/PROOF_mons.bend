# PROOF_mons.bend -- the proofs for LAWS_mons.bend.  The gate:
#
#   bend PROOF_mons.bend            must print ALL PROOFS CHECK
#   bend PROOF_mons.bend --verdict  re-checked by the Lean-proved kernel
#
# House style (PROOF_router.bend / PROOF_mconfig.bend): quantified laws
# go through go-lemmas that match the shrinking argument plus the
# witnesses; {==} closes what normalises; the and-elimination helpers
# are PROOF_router's plain defs (PR.and_elim_l_go / and_elim_r_go /
# lt_ok_nil_absurd -- plain defs re-export across module imports where
# filled laws do not).  The count laws compose with the router's
# publication schedule through the PLAIN bridge PR.newest_at_at
# (newest_at_at in PROOF_router.bend) plus the layer's own transport
# law mon_count_agree: the monitor's MCount recurrence IS the Lane
# recurrence with the rate played by the period, so the whole
# t = q*m + r witness method transfers without a div/mod anywhere.
# The tiny shared-count induction (mon_ticks_shared_go) and the
# arithmetic bricks it needs (add_zero / add_succ) are copied locally
# -- they exist only as filled laws in PROOF_router.bend, which do not
# re-export.
import Base
import ./LAWS_mons.bend as Laws
import ./mons.bend as M
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

# --------------------------------------------------------------------------
# the arithmetic bricks (PROOF_router's Laws.add_zero / Laws.add_succ,
# copied as plain defs -- fills do not re-export)
# --------------------------------------------------------------------------

def add_zero(x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        Nat.add(1n+p, 0n),
        1n+Nat.add(p, 0n),
        1n+p,
        {==},
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, add_zero(p)))

def add_succ(a: Nat, b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        Nat.add(1n+p, 1n+b),
        1n+Nat.add(p, 1n+b),
        1n+Nat.add(1n+p, b),
        {==},
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), Nat.add(1n+p, b),
                   add_succ(p, b)))

# 0 <= x for every x (Nat.cmp does not normalise on symbolic args, so
# this is an induction, not a {==})
def le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      {==}

# a proved equation lifts to the Bool equality test the validator laws use
# (Nat.is_eq goes through Nat.cmp, which does not normalise on symbolic
# args -- eq_refl_b is an induction, not a {==})
def eq_refl_b(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      eq_refl_b(p)

def is_eq_of(a: Nat, b: Nat, h: {a == b : Nat})
    -> {Nat.is_eq(a, b) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_eq(a, b), Nat.is_eq(b, b), True{},
              Equal.cong(Nat, Bool, z => Nat.is_eq(z, b), a, b, h),
              eq_refl_b(b))

# both halves True makes the conjunction True
def and_both(a: Bool, b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool})
    -> {Bool.and(a, b) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(a, b), b, True{},
              Equal.cong(Bool, Bool, z => Bool.and(z, b), a, True{}, ha),
              hb)

# --------------------------------------------------------------------------
# the shared-count induction (PROOF_router's Laws.count_shared, copied:
# the mon_divisor pair law needs the SHARED half of the contrast, and
# the fill does not re-export)
# --------------------------------------------------------------------------

def mon_ticks_shared_go(+t: Nat, +ks: List<&2, Nat>, +m: R.Mon)
    -> {R.mon_n(R.mon_ticks(t, ks, m)) == Nat.add(t, R.mon_n(m)) : Nat}:
  match t:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        R.mon_n(R.mon_ticks(p, ks, R.mon_tick(m))),
        Nat.add(p, 1n+R.mon_n(m)),
        1n+Nat.add(p, R.mon_n(m)),
        mon_ticks_shared_go(p, ks, R.mon_tick(m)),
        add_succ(p, R.mon_n(m)))

# --------------------------------------------------------------------------
# the count laws
# --------------------------------------------------------------------------

# THE transport: the monitor's counter computes the same schedule as a
# router Lane of that period.  Induction on t with the countdown split:
# the wrapping tick (left = 0) publishes on both sides and resets to
# m-1; the holding tick (left = 1+l) decrements on both sides.  The
# recursive calls ARE the goal up to normalisation.
def mc_agree_go(+t: Nat, +m: Nat, +l: Nat, +n: Nat)
    -> {M.mc_n(M.mc_ticks(t, M.MCount{m, l, n}))
          == R.lane_newest(R.steps(t, R.Lane{m, l, n})) : Nat}:
  match t l:
    case 0n _:
      {==}
    case 1n+p 0n:
      mc_agree_go(p, m, Nat.sub(m, 1n), 1n+n)
    case 1n+p 1n+q:
      mc_agree_go(p, m, q, n)

def Laws.mon_count_agree(t, m, l, n):
  mc_agree_go(t, m, l, n)

# mon_rate_count: transport to the lane schedule, then the newest_at
# bridge at n = 0 (the monitor starts with no samples).  The bridge's
# conclusion Nat.add(0n, q) IS q, so the chain closes on the witness
# law exactly.
def mon_rate_count_go(+m: Nat, +q: Nat, +r: Nat,
                      +h: {Nat.is_ge(m, 1n) == True{} : Bool},
                      +hr: {Nat.is_le(r, Nat.sub(m, 1n)) == True{} : Bool})
    -> {M.mon_count(Nat.add(Nat.mul(q, m), r), m) == q : Nat}:
  Equal.trans(Nat,
    M.mc_n(M.mc_ticks(Nat.add(Nat.mul(q, m), r), M.MCount{m, Nat.sub(m, 1n), 0n})),
    R.lane_newest(R.steps(Nat.add(Nat.mul(q, m), r), R.Lane{m, Nat.sub(m, 1n), 0n})),
    q,
    Laws.mon_count_agree(Nat.add(Nat.mul(q, m), r), m, Nat.sub(m, 1n), 0n),
    PR.newest_at_at(m, q, r, 0n, h, hr))

def Laws.mon_rate_count(m, q, r, h, hr):
  mon_rate_count_go(m, q, r, h, hr)

# the boundary convention: no sample at tick 0 -- definitional
def Laws.mon_count_zero(m):
  {==}

# the instance pin: rate 3 over 10 ticks counts 3 (samples at 3, 6, 9)
def Laws.mon_rate_count_instance():
  {==}

# mon_lane_count: the monitor half is mon_rate_count (its own count is
# q), lifted under Nat.add(n, _); the lane half is the newest_at bridge
# at the lane's own IC count n.  Both meet at Nat.add(n, q).
def mon_lane_count_go(+k: Nat, +q: Nat, +r: Nat, +n: Nat,
                      +h: {Nat.is_ge(k, 1n) == True{} : Bool},
                      +hr: {Nat.is_le(r, Nat.sub(k, 1n)) == True{} : Bool})
    -> {Nat.add(n, M.mon_count(Nat.add(Nat.mul(q, k), r), k))
          == R.lane_newest(R.steps(Nat.add(Nat.mul(q, k), r),
                                   R.Lane{k, Nat.sub(k, 1n), n})) : Nat}:
  +hcount = Laws.mon_rate_count(k, q, r, h, hr)
  +hcong = Equal.cong(Nat, Nat, z => Nat.add(n, z),
                      M.mon_count(Nat.add(Nat.mul(q, k), r), k), q, hcount)
  +hbridge = PR.newest_at_at(k, q, r, n, h, hr)
  Equal.trans(Nat,
    Nat.add(n, M.mon_count(Nat.add(Nat.mul(q, k), r), k)),
    Nat.add(n, q),
    R.lane_newest(R.steps(Nat.add(Nat.mul(q, k), r), R.Lane{k, Nat.sub(k, 1n), n})),
    hcong,
    Equal.sym(Nat, R.lane_newest(R.steps(Nat.add(Nat.mul(q, k), r),
                                         R.Lane{k, Nat.sub(k, 1n), n})),
              Nat.add(n, q), hbridge))

def Laws.mon_lane_count(k, q, r, n, h, hr):
  mon_lane_count_go(k, q, r, n, h, hr)

# the instance pin: a lane-period monitor counts publications -- lane
# k=2 with 1 published sample (the IC), 5 master ticks (q=2, r=1): the
# lane is at 1+2=3 published, the monitor counted exactly the 2 new ones
def Laws.mon_lane_count_instance():
  {==}

# --------------------------------------------------------------------------
# the validator: instance pins (pure computation), then the inversion
# family (one and_elim walk per conjunct, the section-6 pattern)
# --------------------------------------------------------------------------

def Laws.mon_ok_good():
  {==}

def Laws.mon_ok_bad_lane():
  {==}

def Laws.mon_ok_bad_rate():
  {==}

# the per-index forms: induction on the monitor list, peeling the
# index.  The Nil case is absurd (i < 0, through PR.lt_ok_nil_absurd);
# the head case is the fold's head pair (lane = left elim, rate = right
# elim); the succ case recurses into the tail with the tail conjunct.
# The peeled witness passes straight through: lt_ok(1n+q, 1n+|tail|)
# and lt_ok(q, |tail|) share the normal form.
def mons_lane_nth_go(+c: R.Config, +mcs: List<&2, M.MonCfg>, +i: Nat,
                     h: R.lt_ok(i, M.mons_len(mcs)),
                     hok: {M.mons_ok(c, mcs) == True{} : Bool})
    -> {M.mon_lane_ok(c, M.nth_moncfg(mcs, i)) == True{} : Bool}:
  match mcs i h:
    case Nil{} _ h:
      Empty.absurd({M.mon_lane_ok(c, M.nth_moncfg(Nil{}, i)) == True{} : Bool},
                   PR.lt_ok_nil_absurd(i, h))
    case mc <> t 0n _:
      PR.and_elim_l_go(M.mon_lane_ok(c, mc), M.mon_rate_ok(mc),
                       PR.and_elim_l_go(Bool.and(M.mon_lane_ok(c, mc), M.mon_rate_ok(mc)),
                                        M.mons_ok(c, t), hok))
    case mc <> t 1n+q hlt:
      mons_lane_nth_go(c, t, q, hlt,
                       PR.and_elim_r_go(Bool.and(M.mon_lane_ok(c, mc), M.mon_rate_ok(mc)),
                                        M.mons_ok(c, t), hok))

def Laws.mons_ok_lane_nth(c, mcs, i, h, hok):
  mons_lane_nth_go(c, mcs, i, h, hok)

def mons_rate_nth_go(+c: R.Config, +mcs: List<&2, M.MonCfg>, +i: Nat,
                     h: R.lt_ok(i, M.mons_len(mcs)),
                     hok: {M.mons_ok(c, mcs) == True{} : Bool})
    -> {M.mon_rate_ok(M.nth_moncfg(mcs, i)) == True{} : Bool}:
  match mcs i h:
    case Nil{} _ h:
      Empty.absurd({M.mon_rate_ok(M.nth_moncfg(Nil{}, i)) == True{} : Bool},
                   PR.lt_ok_nil_absurd(i, h))
    case mc <> t 0n _:
      PR.and_elim_r_go(M.mon_lane_ok(c, mc), M.mon_rate_ok(mc),
                       PR.and_elim_l_go(Bool.and(M.mon_lane_ok(c, mc), M.mon_rate_ok(mc)),
                                        M.mons_ok(c, t), hok))
    case mc <> t 1n+q hlt:
      mons_rate_nth_go(c, t, q, hlt,
                       PR.and_elim_r_go(Bool.and(M.mon_lane_ok(c, mc), M.mon_rate_ok(mc)),
                                        M.mons_ok(c, t), hok))

def Laws.mons_ok_rate_nth(c, mcs, i, h, hok):
  mons_rate_nth_go(c, mcs, i, h, hok)

# --------------------------------------------------------------------------
# the divisor: the per-own-step meaning (the count_shared complement)
# --------------------------------------------------------------------------

# mon_divisor: the monitor's own divisor is its own count 1+q -- one
# sample per completed period, by mon_rate_count at the witness
# (q := 1+q, r := 0; is_le(0, m-1) is definitional) -- while the SHARED
# master count is the full master span (1+q)*m, by the shared-count
# induction.  The pair of is_eq's is the contrast, conjunction by
# and_both.
def mon_divisor_go(+m: Nat, +q: Nat, +ks: List<&2, Nat>,
                   +h: {Nat.is_ge(m, 1n) == True{} : Bool})
    -> {Bool.and(Nat.is_eq(M.mon_count(Nat.mul(1n+q, m), m), Nat.add(1n, q)),
                 Nat.is_eq(R.mon_n(R.mon_ticks(Nat.mul(1n+q, m), ks, R.mon_init())),
                           Nat.mul(1n+q, m)))
          == True{} : Bool}:
  +hcount = Laws.mon_rate_count(m, 1n+q, 0n, h, le_zero(Nat.sub(m, 1n)))
  +hshift = Equal.sym(Nat, Nat.add(Nat.mul(1n+q, m), 0n), Nat.mul(1n+q, m),
                      add_zero(Nat.mul(1n+q, m)))
  +hcount2 = Equal.trans(Nat,
    M.mon_count(Nat.mul(1n+q, m), m),
    M.mon_count(Nat.add(Nat.mul(1n+q, m), 0n), m),
    Nat.add(1n, q),
    Equal.cong(Nat, Nat, z => M.mon_count(z, m),
               Nat.mul(1n+q, m), Nat.add(Nat.mul(1n+q, m), 0n), hshift),
    hcount)
  +hA = is_eq_of(M.mon_count(Nat.mul(1n+q, m), m), Nat.add(1n, q), hcount2)
  +hshared0 = mon_ticks_shared_go(Nat.mul(1n+q, m), ks, R.mon_init())
  +hshared = Equal.trans(Nat,
    R.mon_n(R.mon_ticks(Nat.mul(1n+q, m), ks, R.mon_init())),
    Nat.add(Nat.mul(1n+q, m), 0n),
    Nat.mul(1n+q, m),
    hshared0,
    add_zero(Nat.mul(1n+q, m)))
  +hB = is_eq_of(R.mon_n(R.mon_ticks(Nat.mul(1n+q, m), ks, R.mon_init())),
                 Nat.mul(1n+q, m), hshared)
  and_both(Nat.is_eq(M.mon_count(Nat.mul(1n+q, m), m), Nat.add(1n, q)),
           Nat.is_eq(R.mon_n(R.mon_ticks(Nat.mul(1n+q, m), ks, R.mon_init())),
                     Nat.mul(1n+q, m)),
           hA, hB)

def Laws.mon_divisor(m, q, ks, h):
  mon_divisor_go(m, q, ks, h)

# the instance pin for the intended reading: at rate 3 over 6 master
# ticks the per-subnet monitor divides by 2, the shared count is 6
def Laws.mon_divisor_instance():
  {==}

# --------------------------------------------------------------------------
# P1 part 2 -- the PER-LANE RATES.  The new laws either are the family
# laws INSTANTIATED at the routed rate M.mrate_at(mrs, i) (proofs are the
# instantiation calls) or are the nth-family inductions over the rate
# list itself.  No new arithmetic anywhere; the count law mons_period_count
# reuses mon_rate_count, the composition mons_lane_count_route reuses
# mon_lane_count (whose own proof goes through the newest_at bridge), and
# mons_divisor_route reuses mon_divisor.
# --------------------------------------------------------------------------

# mons_rate_nth: the routed read IS the list's i-th entry.  Induction on
# (mrs, i) with the bound witness -- the lanes_nth_valid pattern; the
# Nil arm is absurd (lt_ok(i, 0n) is Empty).
def mrates_nth_go(+mrs: List<&2, Nat>, +i: Nat,
                   h: R.lt_ok(i, M.mrates_len(mrs)))
    -> {M.mrate_at(mrs, i) == R.nats_nth(mrs, i) : Nat}:
  match mrs i h:
    case Nil{} _ h:
      Empty.absurd({M.mrate_at(Nil{}, i) == R.nats_nth(Nil{}, i) : Nat},
                   PR.lt_ok_nil_absurd(i, h))
    case k <> t 0n _:
      {==}
    case k <> t 1n+q hlt:
      mrates_nth_go(t, q, hlt)

def Laws.mons_rate_nth(mrs, i, h):
  mrates_nth_go(mrs, i, h)

# mons_rate_past_end: the read AT the list's own length lands on rate 0.
# Induction on mrs; the succ arm reduces mrates_len(k <> t) to 1n+|t| and
# the match's 1n+p arm to mrate_at(t, |t|) -- the IH.
def mons_rate_past_end_go(+mrs: List<&2, Nat>)
    -> {M.mrate_at(mrs, M.mrates_len(mrs)) == 0n : Nat}:
  match mrs:
    case Nil{}:
      {==}
    case k <> t:
      mons_rate_past_end_go(t)

def Laws.mons_rate_past_end(mrs):
  mons_rate_past_end_go(mrs)

def Laws.mons_rate_instance_0():
  {==}

def Laws.mons_rate_instance_1():
  {==}

# the count law at the routed rate: mon_rate_count at m := mrate_at(mrs, i)
# -- the instantiation IS the proof.
def Laws.mons_period_count(mrs, i, q, r, h, hg, hr):
  Laws.mon_rate_count(M.mrate_at(mrs, i), q, r, hg, hr)

def Laws.mons_period_count_instance():
  {==}

# the composition at the routed rate: mon_lane_count at k := mrate_at(mrs,
# i) -- the instantiation IS the proof (the lane half of the family law
# already composes through the newest_at bridge).
def Laws.mons_lane_count_route(mrs, i, q, r, n, h, hg, hr):
  Laws.mon_lane_count(M.mrate_at(mrs, i), q, r, n, hg, hr)

def Laws.mons_lane_count_route_instance():
  {==}

# the divisor pinning at the routed rate: mon_divisor at m := mrate_at(mrs,
# i) -- the per-own-step divisor 1+q vs the shared master span (1+q)*m,
# instantiated.
def Laws.mons_divisor_route(mrs, i, q, ks, h, hg):
  Laws.mon_divisor(M.mrate_at(mrs, i), q, ks, hg)

def Laws.mons_divisor_route_instance():
  {==}

# --------------------------------------------------------------------------
# the per-lane validator: instance pins (pure computation) and the
# and-elimination family (one and_elim walk per conjunct, the section-6
# pattern).  mtot_ok's three flat conjuncts: the length conjunct, the rate
# fold, then the base monitor set.
# --------------------------------------------------------------------------

def Laws.mtot_ok_good():
  {==}

def Laws.mtot_ok_bad_rate():
  {==}

def Laws.mtot_ok_bad_short():
  {==}

def Laws.mtot_ok_bad_lane():
  {==}

def Laws.mtot_ok_junk_lane():
  {==}

# the length conjunct is the OUTER and's left half
def Laws.mons_per_ok_len(mrs, mcs, c, hok):
  PR.and_elim_l_go(Nat.is_eq(M.mrates_len(mrs), R.nats_len(R.cfg_lanes(c))),
                   Bool.and(M.rates_ok(mrs), M.mons_ok(c, mcs)),
                   hok)

# the rate fold: peel the length conjunct, then the left half
def Laws.mons_per_ok_rates(mrs, mcs, c, hok):
  PR.and_elim_l_go(M.rates_ok(mrs), M.mons_ok(c, mcs),
                   PR.and_elim_r_go(Nat.is_eq(M.mrates_len(mrs), R.nats_len(R.cfg_lanes(c))),
                                    Bool.and(M.rates_ok(mrs), M.mons_ok(c, mcs)),
                                    hok))

# the base monitor set: peel the length conjunct, then the right half
def Laws.mons_per_ok_mons(mrs, mcs, c, hok):
  PR.and_elim_r_go(M.rates_ok(mrs), M.mons_ok(c, mcs),
                   PR.and_elim_r_go(Nat.is_eq(M.mrates_len(mrs), R.nats_len(R.cfg_lanes(c))),
                                    Bool.and(M.rates_ok(mrs), M.mons_ok(c, mcs)),
                                    hok))

# the per-index rate bound: induction on the rate list, peeling the index
# -- the lanes_nth_valid pattern.  The Nil case is absurd (lt_ok(i, 0n));
# the head case is the fold's head entry (mrate_at(k <> t, 0n) IS k); the
# succ case recurses into the tail with the tail conjunct -- mrate_at's
# 1n+p arm reduces the goal to the recursive call exactly.
def mons_rates_ok_nth_go(+mrs: List<&2, Nat>, +i: Nat,
                         h: R.lt_ok(i, M.mrates_len(mrs)),
                         hok: {M.rates_ok(mrs) == True{} : Bool})
    -> {Nat.is_ge(M.mrate_at(mrs, i), 1n) == True{} : Bool}:
  match mrs i h:
    case Nil{} _ h:
      Empty.absurd({Nat.is_ge(M.mrate_at(Nil{}, i), 1n) == True{} : Bool},
                   PR.lt_ok_nil_absurd(i, h))
    case k <> t 0n _:
      PR.and_elim_l_go(Nat.is_ge(k, 1n), M.rates_ok(t), hok)
    case k <> t 1n+q hlt:
      mons_rates_ok_nth_go(t, q, hlt,
                           PR.and_elim_r_go(Nat.is_ge(k, 1n), M.rates_ok(t), hok))

def Laws.mons_rates_ok_nth(mrs, i, h, hok):
  mons_rates_ok_nth_go(mrs, i, h, hok)

# --------------------------------------------------------------------------
# P1 part 3 -- the BOLD monitor kind and its sample schedule.  The kind
# routing pins are literal reductions; the cover law is the two-arm match;
# the count law is mon_rate_count instantiated at the schedule's period
# (the count machine is SHARED with tavg -- the kind labels only the
# downstream, and the HRF semantics live in compare_*.py).
# --------------------------------------------------------------------------

def Laws.bold_kind_carrier():
  {==}

def Laws.tavg_kind_carrier():
  {==}

def Laws.kind_disjoint():
  {==}

# the constructor cover: two arms, one per kind constructor; each arm
# normalises sch_covers to Bool.or(True, False) / Bool.or(False, True).
def Laws.bold_kind_covers(s):
  match s:
    case M.MonSchedule{M.MKtavg{}, p}:
      {==}
    case M.MonSchedule{M.MKbold{}, p}:
      {==}

def Laws.bold_schedule_shape():
  {==}

def Laws.tavg_schedule_shape():
  {==}

# the BOLD sample schedule: mon_rate_count at the schedule's own period.
# The kind witness hb marks the claim BOLD; the count machinery does not
# branch on it (the sampler is shared), which is exactly the pinned
# division of labour.
def Laws.bold_sample_count(s, q, r, hb, hp, hr):
  Laws.mon_rate_count(M.sch_period(s), q, r, hp, hr)

def Laws.bold_sample_count_instance():
  {==}

# the per-lane BOLD routing: the BOLD schedule of lane i carries the
# lane's routed rate as its period -- definitional (sch_period reads the
# record field).
def Laws.bold_schedule_route(mrs, i):
  {==}

def Laws.bold_schedule_route_instance():
  {==}
