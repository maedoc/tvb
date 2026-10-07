# mons.bend -- the MONITORING VARIETY layer: per-subnet monitors with
# their own rates.
#
# The router's monitor story (router.bend's Mon) is ONE SHARED tavg
# counter: it advances once per master tick for ALL subnets
# (LAWS_router.count_shared), and monitor_zoh_average pins that the
# template's tavg/n divides by that MASTER span.  The gap (the priority
# list's P1): a per-subnet monitor with its own rate -- sample every m
# master ticks, or once per lane tick -- needs its OWN count, and the
# divisor hazard count_shared's comment warns about: a per-subnet
# average must divide by ITS OWN count, not the shared one.
#
# This layer models exactly that, WITHOUT touching router.bend:
#
#   * MonCfg{lane, rate} -- a monitor config: the source lane it
#     monitors (an index into the config's lane list) and its rate in
#     master ticks (sample when the master tick index is a multiple of
#     the rate).
#
#   * the counter, mon_count(t, m) -- a PURE function of the tick count
#     and the rate: the number of sample ticks among master ticks
#     1..t at rate m.  A monitor is a k-periodic publisher with
#     k = rate: it carries a countdown from m and publishes (increments)
#     when the countdown wraps, so its samples land exactly on the
#     master ticks m, 2m, 3m, .. .  MCount is structurally the router's
#     Lane with the period played by the rate and the publication count
#     played by the sample count -- the same recurrence, on purpose:
#     mon_count_agree below PROVES the counter computes the same
#     schedule as a Lane of that period, so the whole Q1 witness
#     machinery (t = q*m + r, no div/mod) transfers to the monitor.
#
#   * the validator, mons_ok(c, mcs) -- every monitor's lane index is
#     inside the config's lane list (the lane EXISTS) and every rate is
#     >= 1 (rate 0 would sample never; the negative control
#     bad/bad_mon_rate.bend rejects it).
#
# BOUNDARY CONVENTION (pinned by LAWS_mons.mon_count_zero and
# mon_rate_count_instance): the monitor does NOT sample at tick 0 --
# the count after 0 ticks is 0, the first sample completes one full
# period (tick m), and over t = q*m + r ticks the count is exactly q.
# This matches the router's lane publication story (the IC is not a
# publication; lane_init starts at count 0 with the countdown at k-1)
# and it is what makes the witness law exact with no +1.

import ./router.bend as R

# --------------------------------------------------------------------------
# the monitor config: source lane + rate in master ticks
# --------------------------------------------------------------------------

type MonCfg is Data:
  MonCfg{lane: Nat, rate: Nat}

def moncfg_lane(+mc: MonCfg) -> Nat:
  match mc:
    case MonCfg{lane, rate}:
      lane

def moncfg_rate(+mc: MonCfg) -> Nat:
  match mc:
    case MonCfg{lane, rate}:
      rate

# --------------------------------------------------------------------------
# the per-monitor counter: a rate-periodic publisher, counted
# --------------------------------------------------------------------------

# the counter state: rate m, countdown left, sample count n.  Same
# recurrence as the router's Lane (publish when the countdown wraps,
# reset to m-1), with the count the monitor divides its average by.
type MCount is Data:
  MCount{m: Nat, left: Nat, n: Nat}

def mc_n(+mc: MCount) -> Nat:
  match mc:
    case MCount{m, left, n}:
      n

# one master tick for one monitor
def mc_step(+mc: MCount) -> MCount:
  match mc:
    case MCount{m, 0n, n}:
      MCount{m, Nat.sub(m, 1n), 1n+n}
    case MCount{m, 1n+l, n}:
      MCount{m, l, n}

# t master ticks for one monitor; the shrinking argument comes first
def mc_ticks(t: Nat, +mc: MCount) -> MCount:
  match t:
    case 0n:
      mc
    case 1n+p:
      mc_ticks(p, mc_step(mc))

# THE pure counter: the number of sample ticks among master ticks 1..t
# at rate m.  Started at the canonical phase (countdown m-1, count 0):
# the first sample lands at tick m, then every m ticks.
def mon_count(t: Nat, +m: Nat) -> Nat:
  mc_n(mc_ticks(t, MCount{m, Nat.sub(m, 1n), 0n}))

# --------------------------------------------------------------------------
# the validator: Bool-valued, computable, run at job load.  The laws
# quantify over monitor sets with the hypothesis {mons_ok == True{}};
# the binary dies on False.  (The router's le_ok-as-Type decider style
# is kept for the index witness in the per-index laws.)
# --------------------------------------------------------------------------

# the monitor's lane exists: the lane index is inside the config's
# lane list (past the end the config has no such subnet)
def mon_lane_ok(+c: R.Config, +mc: MonCfg) -> Bool:
  Nat.is_lt(moncfg_lane(mc), R.nats_len(R.cfg_lanes(c)))

# the monitor's rate is a rate: at least 1 master tick per sample
# (rate 0 samples never and would divide by a stuck 0)
def mon_rate_ok(+mc: MonCfg) -> Bool:
  Nat.is_ge(moncfg_rate(mc), 1n)

def mons_len(mcs: List<&2, MonCfg>) -> Nat:
  match mcs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(1n, mons_len(t))

# nth monitor, defaulting past the end (the nth_proj convention; the
# per-index laws carry lt_ok bounds witnesses so the default branch is
# never trusted)
def nth_moncfg(mcs: List<&2, MonCfg>, i: Nat) -> MonCfg:
  match mcs i:
    case Nil{} _:
      MonCfg{0n, 0n}
    case h <> t 0n:
      h
    case h <> t 1n+p:
      nth_moncfg(t, p)

# THE VALIDATOR: every monitor's lane is in range and every rate >= 1,
# one fold.  The two conjuncts per monitor are spelled FLAT
# (and-of-and), the section-6 and-elimination shape.
def mons_ok(+c: R.Config, mcs: List<&2, MonCfg>) -> Bool:
  match mcs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(Bool.and(mon_lane_ok(c, h), mon_rate_ok(h)), mons_ok(c, t))

# --------------------------------------------------------------------------
# per-lane monitor RATES (SWEEP_LAWS_DESIGN.md P1, second half): each
# subnet/lane carries its OWN monitor period.  The mconfig per-lane idiom:
# a PARALLEL list `mrs` keyed by lane, riding alongside the monitor set --
# lane i's monitor samples every mrate_at(mrs, i) master ticks.
#
# CONVENTIONS (both pinned by laws):
#   * reads PAST the rate list's end land on rate 0n (the nats_nth
#     convention) -- mons_rate_past_end;
#   * the JUNK lane index for a monitor is the rate list's OWN LENGTH (the
#     P4 find_name convention): a monitor at lane mrates_len(mrs) is
#     REJECTED by mtot_ok (mon_lane_ok's lane < nlanes bound against the
#     length conjunct) -- the mtot_ok_junk_lane negative instance;
#   * so the validator NEVER defaults a lane: the length conjunct rejects
#     a short list, the rate fold rejects a rate-0 entry, and the base
#     mons_ok rejects an out-of-range lane (the scheme_ok shape).
# --------------------------------------------------------------------------

def mrates_len(mrs: List<&2, Nat>) -> Nat:
  match mrs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(1n, mrates_len(t))

# lane i's monitor rate: entry i of the per-lane rate list (0n past the
# end, so a lane past the list reads rate 0 -- rejected by the validator's
# rate fold, one way or the other)
def mrate_at(+mrs: List<&2, Nat>, +i: Nat) -> Nat:
  match mrs i:
    case Nil{} _:
      0n
    case h <> t 0n:
      h
    case h <> t 1n+p:
      mrate_at(t, p)

# every RATE in the per-lane list is a rate: at least 1 master tick per
# sample (a 0 entry would sample never and divide its average by a stuck
# count -- the bad/bad_mon_period.bend control)
def rates_ok(mrs: List<&2, Nat>) -> Bool:
  match mrs:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(Nat.is_ge(h, 1n), rates_ok(t))

# THE PER-LANE VALIDATOR, three flat conjuncts (the section-6
# and-elimination shape):
#   (a) ONE rate per lane -- the length conjunct; a short list would
#       leave a lane reading the past-the-end junk (the own-length junk
#       convention makes reads UNREACHABLE, never silently defaulted);
#   (b) every rate >= 1 (rate 0 rejected);
#   (c) the base monitor-set validator mons_ok -- which checks each
#       monitor's LANE against the config's lane list, i.e. the junk lane
#       index = the rate list's own length is rejected there.
# The per-lane layer GATES on the monitor layer, never re-states it.
def mtot_ok(+mrs: List<&2, Nat>, +mcs: List<&2, MonCfg>, +c: R.Config) -> Bool:
  Bool.and(Nat.is_eq(mrates_len(mrs), R.nats_len(R.cfg_lanes(c))),
  Bool.and(rates_ok(mrs),
           mons_ok(c, mcs)))

# --------------------------------------------------------------------------
# BOLD / tavg monitor KINDS (SWEEP_LAWS_DESIGN.md P1, the BOLD half):
# alongside the tavg monitor the layer carries a KIND tag, so a monitor can
# be a BOLD monitor.  Deliberate boundary (the suite's division of labour):
# the BOLD HRF CONVOLUTION is float numerics and lives in the compare_*.py
# drivers -- this layer pins ONLY the kind routing (which constructor
# carries which kind) and the SAMPLE SCHEDULE SHAPE (kind + period in
# master ticks).  The count machine is SHARED: a BOLD monitor samples on
# the same periodic schedule as a tavg monitor of the same period
# (mon_count) -- the kind labels which downstream consumes the samples.
# --------------------------------------------------------------------------

type MonKind is Data:
  MKtavg{}
  MKbold{}

# which kind a constructor carries (the kind routing, in Bool form so the
# laws can use them as conjuncts)
def mkind_is_tavg(+k: MonKind) -> Bool:
  match k:
    case MKtavg{}:
      True{}
    case MKbold{}:
      False{}

def mkind_is_bold(+k: MonKind) -> Bool:
  match k:
    case MKtavg{}:
      False{}
    case MKbold{}:
      True{}

# the sample schedule shape: the monitor KIND plus the period in master
# ticks between samples.  A BOLD monitor is MonSchedule{MKbold{}, p}, a
# tavg monitor MonSchedule{MKtavg{}, p} -- which constructor carries which
# kind is pinned by the kind laws.
type MonSchedule is Data:
  MonSchedule{kind: MonKind, period: Nat}

def sch_kind(+s: MonSchedule) -> MonKind:
  match s:
    case MonSchedule{kind, period}:
      kind

def sch_period(+s: MonSchedule) -> Nat:
  match s:
    case MonSchedule{kind, period}:
      period

def sch_is_tavg(+s: MonSchedule) -> Bool:
  mkind_is_tavg(sch_kind(s))

def sch_is_bold(+s: MonSchedule) -> Bool:
  mkind_is_bold(sch_kind(s))

# every schedule carries one of the two kinds (the constructor cover)
def sch_covers(+s: MonSchedule) -> Bool:
  Bool.or(sch_is_tavg(s), sch_is_bold(s))

# the BOLD schedule of lane i: the BOLD kind at the lane's ROUTED rate
# (rate[i]) -- the per-lane period feeds the BOLD sampler unchanged
def bold_schedule_of(+mrs: List<&2, Nat>, +i: Nat) -> MonSchedule:
  MonSchedule{MKbold{}, mrate_at(mrs, i)}
