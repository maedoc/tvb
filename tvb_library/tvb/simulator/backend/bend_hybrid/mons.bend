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
