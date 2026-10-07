# LAWS_mons.bend -- the claims for the MONITORING VARIETY layer
# (per-subnet monitors with their own rates).  Every law here has its
# proof in PROOF_mons.bend; the gate is tests/run_mons.sh (verdict +
# the rate-0 negative control + the smoke).
#
# The spec is SWEEP_LAWS_DESIGN.md's priority list, P1: today the
# router has ONE shared master count (count_shared / 
# monitor_zoh_average) and the missing piece is the per-subnet monitor
# with its own rate -- the count laws at each rate in the WITNESS form
# (t = q*m + r -> count = q, the newest_at pattern, no Nat.div), the
# composition with the lane's publication count (mon_lane_count), the
# source-lane routing + validation family (lane in range, rate >= 1,
# rate-0 negative control), and the divisor pinning (each monitor
# divides by ITS OWN count -- the per-own-step hazard count_shared's
# comment warns about).
#
# Law style follows LAWS_router.bend sections 1c/1d/6 and
# LAWS_mconfig.bend: the witness-form count laws over t = q*m + r, the
# inversion family (mons_ok == True decomposes per index, the
# and-elimination shape), instance pins (positive AND negative -- they
# pin the INTENDED reading), and the divisor pair law mon_divisor.
import Base
import ./mons.bend as M
import ./router.bend as R

# --------------------------------------------------------------------------
# the instances: a two-lane network, pinned
# --------------------------------------------------------------------------

# two subnets: lane 0 (period 1), lane 1 (period 2); no projections --
# the monitor layer reads only the lane list.
def GOOD_C() -> R.Config:
  R.Config{1n <> 2n <> Nil{}, Nil{}, 1n}

# a well-formed monitor set: lane 0 sampled every 3rd master tick,
# lane 1 every 2nd (its lane period).
def GOOD_MCS() -> List<&2, M.MonCfg>:
  M.MonCfg{0n, 3n} <> M.MonCfg{1n, 2n} <> Nil{}

# the negative lane: monitor for lane 2 of a 2-lane network -- the
# subnet does not exist.
def BAD_LANE_MCS() -> List<&2, M.MonCfg>:
  M.MonCfg{2n, 3n} <> Nil{}

# the negative rate: a rate-0 monitor samples never and would divide
# its average by a stuck 0.
def BAD_RATE_MCS() -> List<&2, M.MonCfg>:
  M.MonCfg{0n, 0n} <> Nil{}

# --------------------------------------------------------------------------
# the count laws (the witness form: t = q*m + r, no div/mod)
# --------------------------------------------------------------------------

# THE transport law: the monitor's counter computes the same schedule
# as a router Lane of that period.  MCount is Lane's recurrence with
# the rate played by the period and the sample count by the publication
# count; this law is WHY the Q1 witness machinery (t = q*m + r)
# transfers to the monitor intact -- every count law below goes through
# it plus the newest_at bridge.
law mon_count_agree:
  for t: Nat
  for +m: Nat
  for +l: Nat
  for +n: Nat
  {M.mc_n(M.mc_ticks(t, M.MCount{m, l, n}))
     == R.lane_newest(R.steps(t, R.Lane{m, l, n})) : Nat}

# mon_rate_count: THE rate-count law.  At rate m (m >= 1), after
# t = q*m + r master ticks (r <= m-1 the remainder witness), the
# monitor's sample count is exactly q: one sample per completed period,
# none for the partial one.  No division anywhere -- the caller
# produces the decomposition, exactly the newest_at method.
law mon_rate_count:
  for +m: Nat
  for q: Nat
  for r: Nat
  for +h: {Nat.is_ge(m, 1n) == True{} : Bool}
  for +hr: {Nat.is_le(r, Nat.sub(m, 1n)) == True{} : Bool}
  {M.mon_count(Nat.add(Nat.mul(q, m), r), m) == q : Nat}

# THE boundary convention, pinned: the monitor does NOT sample at
# tick 0.  The count after 0 ticks is 0 -- sampling starts at tick m
# (the first sample completes one full period), which is what makes
# mon_rate_count exact with no +1.  (The router's lane story agrees:
# lane_init's IC is not a publication.)
law mon_count_zero:
  for +m: Nat
  {M.mon_count(0n, m) == 0n : Nat}

# the instance pin for the convention AND the rate law: a literal
# rate-3 monitor over 10 master ticks counts exactly 3 -- samples at
# ticks 3, 6, 9; tick 0 contributes nothing (a sample-at-tick-0
# convention would make this 4).
law mon_rate_count_instance:
  {M.mon_count(10n, 3n) == 3n : Nat}

# mon_lane_count: THE composition.  At rate = the lane period k, the
# per-subnet monitor's count plus the lane's IC count n is exactly the
# lane's publication count at t = q*k + r: the monitor counts the
# lane's NEW publications (the IC at tick 0 is not a sample), so the
# per-subnet average's divisor is the lane's publication schedule.
# Stated in the witness form; the lane half is the newest_at bridge
# (PR.newest_at_at -- filled laws do not re-export across modules).
law mon_lane_count:
  for +k: Nat
  for q: Nat
  for r: Nat
  for +n: Nat
  for +h: {Nat.is_ge(k, 1n) == True{} : Bool}
  for +hr: {Nat.is_le(r, Nat.sub(k, 1n)) == True{} : Bool}
  {Nat.add(n, M.mon_count(Nat.add(Nat.mul(q, k), r), k))
     == R.lane_newest(R.steps(Nat.add(Nat.mul(q, k), r),
                              R.Lane{k, Nat.sub(k, 1n), n})) : Nat}

# the instance pin: a lane-period monitor counts publications.  Lane
# k=2 started with 1 published sample (the IC), run 5 master ticks
# (q=2, r=1): the lane has published 1+2=3 samples and the monitor at
# rate 2 counts exactly the 2 new ones.
law mon_lane_count_instance:
  {Nat.add(1n, M.mon_count(5n, 2n))
     == R.lane_newest(R.steps(5n, R.Lane{2n, 1n, 1n})) : Nat}

# --------------------------------------------------------------------------
# the validator: positive and negative pins, then the inversion family
# --------------------------------------------------------------------------

# the well-formed monitor set is ACCEPTED: both lanes exist (0 < 2,
# 1 < 2), both rates >= 1.
law mon_ok_good:
  {M.mons_ok(GOOD_C(), GOOD_MCS()) == True{} : Bool}

# the negative lane instance: a monitor for lane 2 of a 2-lane network
# is REJECTED -- the subnet does not exist.
law mon_ok_bad_lane:
  {M.mons_ok(GOOD_C(), BAD_LANE_MCS()) == False{} : Bool}

# the negative rate instance: a rate-0 monitor is REJECTED.
law mon_ok_bad_rate:
  {M.mons_ok(GOOD_C(), BAD_RATE_MCS()) == False{} : Bool}

# --------------------------------------------------------------------------
# the inversion family (the section-6 and-elim pattern): mons_ok ==
# True decomposes per index.  The binary dies on False, so the
# interesting facts are CONDITIONAL on acceptance.
# --------------------------------------------------------------------------

# the lane bound at index i (in bounds): every accepted monitor's lane
# exists -- the fold is not just true of the fold, every reachable
# monitor passes its validator.
law mons_ok_lane_nth:
  for +c: R.Config
  for +mcs: List<&2, M.MonCfg>
  for i: Nat
  for h: R.lt_ok(i, M.mons_len(mcs))
  for +hok: {M.mons_ok(c, mcs) == True{} : Bool}
  {M.mon_lane_ok(c, M.nth_moncfg(mcs, i)) == True{} : Bool}

# the rate bound at index i (in bounds): every accepted monitor's rate
# is at least 1.
law mons_ok_rate_nth:
  for +c: R.Config
  for +mcs: List<&2, M.MonCfg>
  for i: Nat
  for h: R.lt_ok(i, M.mons_len(mcs))
  for +hok: {M.mons_ok(c, mcs) == True{} : Bool}
  {M.mon_rate_ok(M.nth_moncfg(mcs, i)) == True{} : Bool}

# --------------------------------------------------------------------------
# the divisor: the per-own-step meaning (the count_shared complement)
# --------------------------------------------------------------------------

# mon_divisor: WHICH count the per-subnet monitor's average divides by.
# After (1+q) full monitor periods -- t = (1+q)*m master ticks -- the
# monitor's own divisor is its own sample count 1+q (one sample per
# period), while the SHARED master count is the full master span
# (1+q)*m.  The two differ whenever m >= 2: the per-subnet average is a
# PER-OWN-STEP average (divides by its own count), the exact complement
# of count_shared/monitor_zoh_average, which pin the SHARED tavg's
# divisor as the master span.  A wiring that divides the per-subnet
# average by the shared count (or vice versa) breaks this law.
law mon_divisor:
  for +m: Nat
  for q: Nat
  for +ks: List<&2, Nat>
  for +h: {Nat.is_ge(m, 1n) == True{} : Bool}
  {Bool.and(Nat.is_eq(M.mon_count(Nat.mul(1n+q, m), m), Nat.add(1n, q)),
            Nat.is_eq(R.mon_n(R.mon_ticks(Nat.mul(1n+q, m), ks, R.mon_init())),
                      Nat.mul(1n+q, m)))
     == True{} : Bool}

# the instance pin for the intended reading: at rate 3 over 6 master
# ticks the per-subnet monitor divides by 2 (samples at 3 and 6) while
# the shared master count is 6 -- the literals spell the divergence.
law mon_divisor_instance:
  {Bool.and(Nat.is_eq(M.mon_count(6n, 3n), 2n),
            Nat.is_eq(R.mon_n(R.mon_ticks(6n, 1n <> Nil{}, R.mon_init())), 6n))
     == True{} : Bool}

# --------------------------------------------------------------------------
# P1, part 2 -- the PER-LANE RATES (each subnet/lane carries its OWN
# monitor period).  The mconfig per-lane idiom: a parallel rate list mrs
# keyed by lane; lane i's monitor samples every M.mrate_at(mrs, i) master
# ticks.  The routing (the nth family), the junk conventions, the count
# law at EACH rate, the composition with the lane's publication count, and
# the divisor pinning -- all in the routed form, so the proofs instantiate
# the family laws at the routed rate (no new arithmetic anywhere).
# --------------------------------------------------------------------------

# the instances: GOOD_C's two lanes get rates 3 and 2 -- lane 0's monitor
# samples every 3rd master tick, lane 1's every 2nd.
def GOOD_MRS() -> List<&2, Nat>:
  3n <> 2n <> Nil{}

# the negative rate list: lane 0's monitor samples every ZERO master ticks
# (rejected by the rate fold).
def RATE0_MRS() -> List<&2, Nat>:
  0n <> 2n <> Nil{}

# the short rate list: lane 1 has NO rate -- the junk read (own-length /
# past-end conventions) must never be trusted, so the LENGTH conjunct
# rejects it.
def SHORT_MRS() -> List<&2, Nat>:
  3n <> Nil{}

# --------------------------------------------------------------------------
# (a) the routing: lane i's monitor reads rate[i]
# --------------------------------------------------------------------------

# the routing law, the nth family: inside the rate list the routed read IS
# the list's i-th entry.  (Bounded by lt_ok -- the past-end read is the
# junk convention, pinned separately below.)
law mons_rate_nth:
  for +mrs: List<&2, Nat>
  for i: Nat
  for h: R.lt_ok(i, M.mrates_len(mrs))
  {M.mrate_at(mrs, i) == R.nats_nth(mrs, i) : Nat}

# the past-end read lands on rate 0 (the nats_nth convention): a lane
# whose rate was never configured reads a rate-0 -- and rate 0 is exactly
# what the validator's rate fold rejects.  (The JUNK lane index = the
# rate list's OWN length is the OTHER half: rejected by the lane bound,
# pinned by the mtot_ok_junk_lane negative instance below -- the P4
# find_name convention.)
law mons_rate_past_end:
  for +mrs: List<&2, Nat>
  {M.mrate_at(mrs, M.mrates_len(mrs)) == 0n : Nat}

# the instance pins: lane 0 of the literal rate list reads 3, lane 1
# reads 2 (the routing); the read AT the list's own length is the junk 0.
law mons_rate_instance_0:
  {M.mrate_at(3n <> 2n <> Nil{}, 0n) == 3n : Nat}

law mons_rate_instance_1:
  {M.mrate_at(3n <> 2n <> Nil{}, 1n) == 2n : Nat}

# --------------------------------------------------------------------------
# (b) the count law at EACH rate: t = q*m + r -> count = q, at the ROUTED
# per-lane rate m = mrate_at(mrs, i).  The newest_at witness form -- the
# caller decomposes, no Nat.div anywhere.  (This is the family law
# mon_rate_count instantiated at the routed rate; the proof is the
# instantiation.)
# --------------------------------------------------------------------------

law mons_period_count:
  for +mrs: List<&2, Nat>
  for +i: Nat
  for q: Nat
  for r: Nat
  for h: R.lt_ok(i, M.mrates_len(mrs))
  for +hg: {Nat.is_ge(M.mrate_at(mrs, i), 1n) == True{} : Bool}
  for +hr: {Nat.is_le(r, Nat.sub(M.mrate_at(mrs, i), 1n)) == True{} : Bool}
  {M.mon_count(Nat.add(Nat.mul(q, M.mrate_at(mrs, i)), r), M.mrate_at(mrs, i)) == q : Nat}

# instance pin: lane 0's rate is 3; over 10 master ticks (q = 3, r = 1)
# its monitor counted exactly 3 samples (ticks 3, 6, 9).
law mons_period_count_instance:
  {M.mon_count(10n, M.mrate_at(3n <> 2n <> Nil{}, 0n)) == 3n : Nat}

# --------------------------------------------------------------------------
# (c) the composition: the per-lane monitor's count == that lane's
# publication count.  At rate = the lane period the monitor counts the
# lane's NEW publications beside the lane's IC count n -- the routed form
# of mon_lane_count (the monitor at rate[i] tracks a lane of period
# rate[i]), composed through the newest_at bridge by the family law.
# --------------------------------------------------------------------------

law mons_lane_count_route:
  for +mrs: List<&2, Nat>
  for +i: Nat
  for q: Nat
  for r: Nat
  for +n: Nat
  for h: R.lt_ok(i, M.mrates_len(mrs))
  for +hg: {Nat.is_ge(M.mrate_at(mrs, i), 1n) == True{} : Bool}
  for +hr: {Nat.is_le(r, Nat.sub(M.mrate_at(mrs, i), 1n)) == True{} : Bool}
  {Nat.add(n, M.mon_count(Nat.add(Nat.mul(q, M.mrate_at(mrs, i)), r), M.mrate_at(mrs, i)))
     == R.lane_newest(R.steps(Nat.add(Nat.mul(q, M.mrate_at(mrs, i)), r),
                              R.Lane{M.mrate_at(mrs, i), Nat.sub(M.mrate_at(mrs, i), 1n), n}))
        : Nat}

# instance pin: lane 1's routed rate is 2 (its lane period).  Lane started
# with 1 published sample (the IC), run 5 master ticks (q = 2, r = 1): the
# lane is at 1+2 = 3 published, the monitor counted exactly the 2 new ones.
law mons_lane_count_route_instance:
  {Nat.add(1n, M.mon_count(5n, M.mrate_at(3n <> 2n <> Nil{}, 1n)))
     == R.lane_newest(R.steps(5n, R.Lane{M.mrate_at(3n <> 2n <> Nil{}, 1n),
                                          Nat.sub(M.mrate_at(3n <> 2n <> Nil{}, 1n), 1n),
                                          1n}))
        : Nat}

# --------------------------------------------------------------------------
# (d) the DIVISOR pinning, routed: each monitor divides by ITS OWN count,
# not the shared one -- the per-own-step hazard count_shared's comment
# warns about.  After (1+q) full monitor periods at the routed rate m =
# mrate_at(mrs, i), the per-lane average divides by its own count 1+q
# (one sample per period) while the SHARED master count is the full master
# span (1+q)*m.  A wiring that divides the per-lane average by the shared
# count breaks this law.
# --------------------------------------------------------------------------

law mons_divisor_route:
  for +mrs: List<&2, Nat>
  for +i: Nat
  for q: Nat
  for +ks: List<&2, Nat>
  for h: R.lt_ok(i, M.mrates_len(mrs))
  for +hg: {Nat.is_ge(M.mrate_at(mrs, i), 1n) == True{} : Bool}
  {Bool.and(Nat.is_eq(M.mon_count(Nat.mul(1n+q, M.mrate_at(mrs, i)), M.mrate_at(mrs, i)), Nat.add(1n, q)),
            Nat.is_eq(R.mon_n(R.mon_ticks(Nat.mul(1n+q, M.mrate_at(mrs, i)), ks, R.mon_init())),
                      Nat.mul(1n+q, M.mrate_at(mrs, i))))
     == True{} : Bool}

# instance pin for the intended reading, routed: lane 0's rate is 3; over
# 6 master ticks (q = 1) the per-lane monitor divides by its OWN count 2
# while the shared master count is 6.
law mons_divisor_route_instance:
  {Bool.and(Nat.is_eq(M.mon_count(6n, M.mrate_at(3n <> 2n <> Nil{}, 0n)), 2n),
            Nat.is_eq(R.mon_n(R.mon_ticks(6n, 1n <> Nil{}, R.mon_init())), 6n))
     == True{} : Bool}

# --------------------------------------------------------------------------
# the per-lane validator: positive / negative instance pins and the
# and-elimination family (the section-6 shape).  mtot_ok = ONE rate per
# lane (the length conjunct) /\( every rate >= 1 /\ the base monitor set
# passes mons_ok -- which checks every monitor's lane against the config's
# lane list).
# --------------------------------------------------------------------------

# the well-formed per-lane rate list is ACCEPTED: one rate per lane (2 for
# the 2-lane GOOD_C), both rates >= 1, the base monitor set ok.
law mtot_ok_good:
  {M.mtot_ok(GOOD_MRS(), GOOD_MCS(), GOOD_C()) == True{} : Bool}

# a rate-0 entry is REJECTED (samples never; a stuck divisor).
law mtot_ok_bad_rate:
  {M.mtot_ok(RATE0_MRS(), GOOD_MCS(), GOOD_C()) == False{} : Bool}

# a SHORT rate list is REJECTED: lane 1 has no rate, and the junk read
# must never be trusted -- the length conjunct (one rate per lane) is
# load-bearing, NOT a decoration.
law mtot_ok_bad_short:
  {M.mtot_ok(SHORT_MRS(), GOOD_MCS(), GOOD_C()) == False{} : Bool}

# the base monitor validator still applies: a monitor for a nonexistent
# subnet is REJECTED by the per-lane validator too (it gates on mons_ok).
law mtot_ok_bad_lane:
  {M.mtot_ok(GOOD_MRS(), BAD_LANE_MCS(), GOOD_C()) == False{} : Bool}

# THE JUNK-INDEX CONVENTION, pinned negatively: the junk lane index for a
# monitor is the rate list's OWN LENGTH (the P4 find_name convention), and
# the lane bound rejects exactly that -- a monitor at lane
# mrates_len(GOOD_MRS()) = 2 of the 2-lane network is rejected.
law mtot_ok_junk_lane:
  {M.mtot_ok(GOOD_MRS(), M.MonCfg{M.mrates_len(GOOD_MRS()), 3n} <> Nil{}, GOOD_C())
     == False{} : Bool}

# the and-elims: each conjunct of mtot_ok decomposes under acceptance --
# one rate per lane (the length conjunct), the rate fold, and the base
# monitor set.  The binary dies on False, so the interesting facts are
# CONDITIONAL on acceptance.
law mons_per_ok_len:
  for +mrs: List<&2, Nat>
  for +mcs: List<&2, M.MonCfg>
  for +c: R.Config
  for +hok: {M.mtot_ok(mrs, mcs, c) == True{} : Bool}
  {Nat.is_eq(M.mrates_len(mrs), R.nats_len(R.cfg_lanes(c))) == True{} : Bool}

law mons_per_ok_rates:
  for +mrs: List<&2, Nat>
  for +mcs: List<&2, M.MonCfg>
  for +c: R.Config
  for +hok: {M.mtot_ok(mrs, mcs, c) == True{} : Bool}
  {M.rates_ok(mrs) == True{} : Bool}

law mons_per_ok_mons:
  for +mrs: List<&2, Nat>
  for +mcs: List<&2, M.MonCfg>
  for +c: R.Config
  for +hok: {M.mtot_ok(mrs, mcs, c) == True{} : Bool}
  {M.mons_ok(c, mcs) == True{} : Bool}

# the per-index rate bound (the lanes_nth_valid pattern over the rate
# list): every accepted rate list's i-th entry is a rate -- the fold is
# not just true of the whole, every reachable entry passes.
law mons_rates_ok_nth:
  for +mrs: List<&2, Nat>
  for i: Nat
  for h: R.lt_ok(i, M.mrates_len(mrs))
  for +hok: {M.rates_ok(mrs) == True{} : Bool}
  {Nat.is_ge(M.mrate_at(mrs, i), 1n) == True{} : Bool}

# --------------------------------------------------------------------------
# P1, part 3 -- the BOLD monitor KIND and its sample schedule.  Boundary
# (the suite's division of labour): the BOLD HRF CONVOLUTION is float
# numerics and belongs to the compare_*.py drivers; the law layer pins
# ONLY the kind routing (which constructor carries tavg vs bold) and the
# schedule SHAPE (kind + period).  The count machine is shared: a BOLD
# monitor samples on the same periodic schedule as a tavg monitor of the
# same period, and the kind labels only which downstream consumes the
# samples.
# --------------------------------------------------------------------------

# the instance pins: the per-lane rate list and the BOLD schedule the
# negative controls (bad/bad_bold.bend) try to mis-route.
def GOOD_BOLD() -> M.MonSchedule:
  M.MonSchedule{M.MKbold{}, 2n}

# which constructor carries which kind (the kind routing):
law bold_kind_carrier:
  {M.mkind_is_bold(M.MKbold{}) == True{} : Bool}

law tavg_kind_carrier:
  {M.mkind_is_tavg(M.MKtavg{}) == True{} : Bool}

# the constructors are DISJOINT: the tavg constructor is never bold and
# the bold constructor is never tavg -- a schedule is exactly one kind.
law kind_disjoint:
  {Bool.and(M.mkind_is_bold(M.MKtavg{}), M.mkind_is_tavg(M.MKbold{}))
     == False{} : Bool}

# the constructor cover: EVERY schedule carries one of the two kinds (the
# two-constructor structural pin -- a third kind would break it).
law bold_kind_covers:
  for +s: M.MonSchedule
  {M.sch_covers(s) == True{} : Bool}

# the schedule SHAPE: a BOLD schedule is (MKbold{}, period) -- the kind
# field routes to bold, the period field is the sampling period.  Small
# literal witness (the verdict-budget lesson).
law bold_schedule_shape:
  {Bool.and(M.mkind_is_bold(M.sch_kind(GOOD_BOLD())),
            Nat.is_eq(M.sch_period(GOOD_BOLD()), 2n))
     == True{} : Bool}

# the tavg schedule shape: (MKtavg{}, period) -- same record, other kind.
law tavg_schedule_shape:
  {Bool.and(M.mkind_is_tavg(M.sch_kind(M.MonSchedule{M.MKtavg{}, 1n})),
            Nat.is_eq(M.sch_period(M.MonSchedule{M.MKtavg{}, 1n}), 1n))
     == True{} : Bool}

# the BOLD sample schedule: a BOLD monitor's count obeys the SAME periodic
# machine (t = q*p + r -> count = q, p the schedule's period) -- the
# schedule shape pinned at the count level, newest_at witness form, the
# kind witness (hb) marking the claim BOLD.
law bold_sample_count:
  for +s: M.MonSchedule
  for q: Nat
  for r: Nat
  for +hb: {M.mkind_is_bold(M.sch_kind(s)) == True{} : Bool}
  for +hp: {Nat.is_ge(M.sch_period(s), 1n) == True{} : Bool}
  for +hr: {Nat.is_le(r, Nat.sub(M.sch_period(s), 1n)) == True{} : Bool}
  {M.mon_count(Nat.add(Nat.mul(q, M.sch_period(s)), r), M.sch_period(s)) == q : Nat}

# instance pin: GOOD_BOLD (kind bold, period 2) over 5 master ticks
# (q = 2, r = 1) counts 2 samples (ticks 2 and 4) -- the sample schedule
# shape at a small literal.
law bold_sample_count_instance:
  {M.mon_count(5n, M.sch_period(GOOD_BOLD())) == 2n : Nat}

# the per-lane BOLD routing: the BOLD schedule of lane i carries the
# lane's ROUTED rate as its period -- BOLD samples on rate[i], the two P1
# halves joined at the schedule record.
law bold_schedule_route:
  for +mrs: List<&2, Nat>
  for i: Nat
  {M.sch_period(M.bold_schedule_of(mrs, i)) == M.mrate_at(mrs, i) : Nat}

# instance pin: lane 0's BOLD schedule period IS rate[0] = 3.
law bold_schedule_route_instance:
  {M.sch_period(M.bold_schedule_of(3n <> 2n <> Nil{}, 0n)) == 3n : Nat}
