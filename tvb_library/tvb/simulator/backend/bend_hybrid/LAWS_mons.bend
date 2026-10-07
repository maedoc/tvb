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
