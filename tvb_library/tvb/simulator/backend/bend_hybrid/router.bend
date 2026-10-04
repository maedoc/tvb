# router.bend -- a Bend-native routing core for a hybrid network.
#
# NOT a port of nb_hybrid / cpp_hybrid conventions.  This is the hybrid
# simulator re-cast as a ROUTER: the configuration (subnets, projections,
# monitors) is a tree of Nats, routing is a pure traversal of that tree over
# master ticks, and floats appear only at the leaves (the kernel that
# consumes a routed Line).  Everything in this file is Nat / Data, so every
# interesting property is provable by structural induction over the tick
# stream -- no div/mod lemma library needed, because the schedule is CARRIED
# (per-lane counters), not computed in closed form.
#
# Conventions (ours, pinned here -- reconciliation with the numba template's
# 1-based tick is a separate, explicit step):
#
#   * the master tick is 0-based;
#   * subnet ("lane") j steps once every k_j >= 1 master ticks;
#   * a Lane carries {k, left, newest}:
#       k      -- period in master ticks (config, fixed)
#       left   -- master ticks remaining until this lane's next step
#                 (counts down k-1 .. 0; at 0 the lane steps and publishes)
#       newest -- index of the newest published sample; sample 0 is the
#                 initial condition, so newest == number of steps taken;
#   * phase (interpolation position) is derived: num = k-1-left, den = k;
#   * a projection reads its SOURCE lane delayed by d source samples;
#   * delay d in {samples of the source lane}; the zero-delay read asks for
#     a sample one past the newest, so the clamp to ZOH is load-bearing
#     (proved: Laws.clamp_necessary);
#   * reads saturating below sample 0 land on the IC fill (sub saturates),
#     matching the engines' pre-filled rings.
#
# Step-then-read: within one master tick every due lane publishes first, then
# projections route.  One tick of the whole tree is `tick`.

import Base

# --------------------------------------------------------------------------
# Lanes: one per subnet.  The schedule state.
# --------------------------------------------------------------------------

type Lane is Data:
  Lane{k: Nat, left: Nat, newest: Nat}

def lane_k(l: Lane) -> Nat:
  match l:
    case Lane{k, left, newest}:
      k

def lane_left(l: Lane) -> Nat:
  match l:
    case Lane{k, left, newest}:
      left

def lane_newest(l: Lane) -> Nat:
  match l:
    case Lane{k, left, newest}:
      newest

# one master tick for one lane: publish when the countdown wraps.
# NOTE: declared before step_lane (no forward references, no mutual
# recursion anywhere in this file).
def step_go(left: Nat, +l: Lane) -> Lane:
  match left:
    case 0n:
      Lane{lane_k(l), Nat.sub(lane_k(l), 1n), 1n+lane_newest(l)}
    case 1n+p:
      Lane{lane_k(l), p, lane_newest(l)}

def step_lane(+l: Lane) -> Lane:
  step_go(lane_left(l), l)

# t master ticks for one lane; the shrinking argument comes first
def steps(t: Nat, +l: Lane) -> Lane:
  match t:
    case 0n:
      l
    case 1n+p:
      steps(p, step_lane(l))

# a fresh lane of period k holding only its IC (sample 0)
def lane_init(+k: Nat) -> Lane:
  Lane{k, Nat.sub(k, 1n), 0n}

# interpolation fraction carried as Nats: num/den in [0, 1).
# The float appears only at the leaf, as F32.of(num)/F32.of(den).
def lane_num(+l: Lane) -> Nat:
  Nat.sub(Nat.sub(lane_k(l), 1n), lane_left(l))

# --------------------------------------------------------------------------
# Lines: one routed read.  This is what a projection hands to the kernel:
# read source samples i0 and i1, blend with num/den, average win samples
# ending at i0 when win > 0 (the anti-alias / Q2 mode).  All Nat.
# --------------------------------------------------------------------------

type Line is Data:
  Line{i0: Nat, i1: Nat, num: Nat, den: Nat, win: Nat}

def l_i0(+l: Line) -> Nat:
  match l:
    case Line{i0, i1, num, den, win}:
      i0

def l_i1(+l: Line) -> Nat:
  match l:
    case Line{i0, i1, num, den, win}:
      i1

def l_num(+l: Line) -> Nat:
  match l:
    case Line{i0, i1, num, den, win}:
      num

def l_den(+l: Line) -> Nat:
  match l:
    case Line{i0, i1, num, den, win}:
      den

def l_win(+l: Line) -> Nat:
  match l:
    case Line{i0, i1, num, den, win}:
      win

# THE routing decision, and the only place the ZOH clamp lives.
#   d = 0 : the asked-for ceil sample is one past the newest (proved:
#           Laws.clamp_necessary), so clamp i1 = i0 and zero the fraction;
#   d >= 1: i0 = n-d, i1 = n-(d-1) = i0+1 are both published (proved:
#           Laws.read_fresh), and the fraction passes through.
def route_read(+n: Nat, +d: Nat, +num: Nat, +den: Nat, +win: Nat) -> Line:
  match d:
    case 0n:
      Line{n, n, 0n, den, win}
    case 1n+dp:
      Line{Nat.sub(n, 1n+dp), Nat.sub(n, dp), num, den, win}

# --------------------------------------------------------------------------
# The configuration tree: lanes + projections + a global history horizon.
# A projection is a routing edge: source lane, target lane, delay in source
# samples, averaging window (0 = point read), target coupling slot.
# --------------------------------------------------------------------------

type Proj is Data:
  Proj{src: Nat, tgt: Nat, d: Nat, win: Nat, tc: Nat}

def proj_src(+p: Proj) -> Nat:
  match p:
    case Proj{src, tgt, d, win, tc}:
      src

def proj_tgt(+p: Proj) -> Nat:
  match p:
    case Proj{src, tgt, d, win, tc}:
      tgt

def proj_d(+p: Proj) -> Nat:
  match p:
    case Proj{src, tgt, d, win, tc}:
      d

def proj_win(+p: Proj) -> Nat:
  match p:
    case Proj{src, tgt, d, win, tc}:
      win

def proj_tc(+p: Proj) -> Nat:
  match p:
    case Proj{src, tgt, d, win, tc}:
      tc

type Config is Data:
  Config{lanes: List<&2, Nat>, projs: List<&2, Proj>, horizon: Nat}

def cfg_lanes(+c: Config) -> List<&2, Nat>:
  match c:
    case Config{lanes, projs, horizon}:
      lanes

def cfg_projs(+c: Config) -> List<&2, Proj>:
  match c:
    case Config{lanes, projs, horizon}:
      projs

def cfg_horizon(+c: Config) -> Nat:
  match c:
    case Config{lanes, projs, horizon}:
      horizon

# --------------------------------------------------------------------------
# One tick of the whole tree: step every lane, then route every projection.
# This is the engine skeleton at Nat level; a run's routing tables are the
# iteration of `tick`.
# --------------------------------------------------------------------------

# build the initial lanes from the period list, at tick 0
# (each holding only its IC), then step them once
def init_lanes(ks: List<&2, Nat>) -> List<&2, Lane>:
  match ks:
    case Nil{}:
      Nil{}
    case h <> t:
      lane_init(h) <> init_lanes(t)

def lanes_step(ls: List<&2, Lane>) -> List<&2, Lane>:
  match ls:
    case Nil{}:
      Nil{}
    case h <> t:
      step_lane(h) <> lanes_step(t)

def nth_lane(ls: List<&2, Lane>, i: Nat) -> Lane:
  match ls i:
    case Nil{} _:
      Lane{1n, 0n, 0n}   # unreachable under ok(cfg) once src < nlanes: the
                         # proj_src_bounded + nth_init_* laws (LAWS_router)
    case h <> t 0n:
      h
    case h <> t 1n+p:
      nth_lane(t, p)

def lanes_len(ls: List<&2, Lane>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(1n, lanes_len(t))

def lines_len(ls: List<&2, Line>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(1n, lines_len(t))

def projs_len(ps: List<&2, Proj>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(1n, projs_len(t))

def route_proj(+ls: List<&2, Lane>, +p: Proj) -> Line:
  route_read(lane_newest(nth_lane(ls, proj_src(p))), proj_d(p),
             lane_num(nth_lane(ls, proj_src(p))),
             lane_k(nth_lane(ls, proj_src(p))), proj_win(p))

def route_all(+ls: List<&2, Lane>, ps: List<&2, Proj>) -> List<&2, Line>:
  match ps:
    case Nil{}:
      Nil{}
    case h <> t:
      route_proj(ls, h) <> route_all(ls, t)

def nth_line(ls: List<&2, Line>, i: Nat) -> Line:
  match ls i:
    case Nil{} _:
      Line{0n, 0n, 0n, 1n, 0n}
    case h <> t 0n:
      h
    case h <> t 1n+p:
      nth_line(t, p)

def nth_proj(ps: List<&2, Proj>, i: Nat) -> Proj:
  match ps i:
    case Nil{} _:
      Proj{0n, 0n, 0n, 0n, 0n}
    case h <> t 0n:
      h
    case h <> t 1n+p:
      nth_proj(t, p)

type Tick is Data:
  Tick{lanes: List<&2, Lane>, lines: List<&2, Line>}

def tick_lanes(+t: Tick) -> List<&2, Lane>:
  match t:
    case Tick{lanes, lines}:
      lanes

def tick_lines(+t: Tick) -> List<&2, Line>:
  match t:
    case Tick{lanes, lines}:
      lines

def tick(ls: List<&2, Lane>, +ps: List<&2, Proj>) -> Tick:
  +stepped = lanes_step(ls)
  Tick{stepped, route_all(stepped, ps)}

def ticks(t: Nat, +ls: List<&2, Lane>, +ps: List<&2, Proj>) -> Tick:
  match t:
    case 0n:
      Tick{ls, route_all(ls, ps)}
    case 1n+p:
      ticks(p, tick_lanes(tick(ls, ps)), ps)

# --------------------------------------------------------------------------
# Monitors: the temporal-average (tavg) bookkeeping, at Nat level.
#
# The template's monitor semantics (nb-hybrid-sim.py.mako L1031/L1052/L1259):
#
#   * per master tick, AFTER the (conditional) integrate, the CURRENT state
#     of EVERY subnet is accumulated into that subnet's tavg buffer;
#   * ONE SHARED tavg_count is incremented once per master tick for ALL
#     subnets -- it is a property of the master clock, not of any lane;
#   * the emitted sample is tavg/n with n = the count, i.e. the average of
#     the ZOH-held trajectories over master time.
#
# A slow lane (k > 1) is integrated only on its due ticks, so between due
# ticks it CONTRIBUTES its held (ZOH) state every master tick: its average
# is a master-time average of the hold, not an average of its own steps.
# Which held sample lands in which tick is already proved (lane_hold,
# due_iff_publishes, period_from_init); Mon just carries the count that
# divides the sum, which is why the two laws below quantify over lane
# periods k and never mention them in the result.
#
# Mon is threaded through the ticks exactly like the lane list -- pure,
# Nat-only, no div/mod, induction over the tick stream as usual.
# --------------------------------------------------------------------------
type Mon is Data:
  Mon{n: Nat}

def mon_n(+m: Mon) -> Nat:
  match m:
    case Mon{n}:
      n

def mon_init() -> Mon:
  Mon{0n}

def mon_tick(+m: Mon) -> Mon:
  Mon{1n+mon_n(m)}

def mon_ticks(t: Nat, +ks: List<&2, Nat>, +m: Mon) -> Mon:
  match t:
    case 0n:
      m
    case 1n+p:
      mon_ticks(p, ks, mon_tick(m))

# --------------------------------------------------------------------------
# Validators: Bool-valued, computable, run at job load.  The laws quantify
# over configs with the hypothesis {ok(cfg) == True{}}; the binary dies on
# False.  (The le_ok-as-Type decider style is kept for the witness-carrying
# constructor below and the negative tests.)
# --------------------------------------------------------------------------

def lanes_ok(ks: List<&2, Nat>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(Nat.is_ge(h, 1n), lanes_ok(t))

def proj_shape_ok(+nlanes: Nat, +horizon: Nat, +p: Proj) -> Bool:
  Bool.and(Nat.is_lt(proj_src(p), nlanes),
  Bool.and(Nat.is_lt(proj_tgt(p), nlanes),
  Bool.and(Nat.is_le(Nat.add(proj_d(p), 1n), horizon),
           Nat.is_le(Nat.add(proj_d(p), proj_win(p)), horizon))))

def projs_shape_ok(+nlanes: Nat, +horizon: Nat, ps: List<&2, Proj>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(proj_shape_ok(nlanes, horizon, h), projs_shape_ok(nlanes, horizon, t))

# two projections clash iff they write the SAME (target lane, target slot):
# float += is order-dependent, so a clash is observable nondeterminism
def proj_clash(+a: Proj, +b: Proj) -> Bool:
  Bool.and(Nat.is_eq(proj_tgt(a), proj_tgt(b)), Nat.is_eq(proj_tc(a), proj_tc(b)))

def no_clash(+a: Proj, ps: List<&2, Proj>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(Bool.not(proj_clash(a, h)), no_clash(a, t))

def writes_unique(ps: List<&2, Proj>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case h <> +t:
      Bool.and(no_clash(h, t), writes_unique(t))

def nats_len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(1n, nats_len(t))

# nth element of a Nat list, defaulting to 0 past the end (the same
# default-past-end convention as nth_lane/nth_proj; the per-index laws
# carry lt_ok bounds witnesses so the default branch is never trusted)
def nats_nth(xs: List<&2, Nat>, i: Nat) -> Nat:
  match xs i:
    case Nil{} _:
      0n
    case h <> t 0n:
      h
    case h <> t 1n+p:
      nats_nth(t, p)

def ok(+c: Config) -> Bool:
  Bool.and(lanes_ok(cfg_lanes(c)),
  Bool.and(projs_shape_ok(nats_len(cfg_lanes(c)), cfg_horizon(c), cfg_projs(c)),
           writes_unique(cfg_projs(c))))

# the capacity gate, the engine-side half of the ring contract: the
# history backend's ring must hold the whole horizon, or two ticks one
# horizon apart would land on the SAME slot (the aliasing bad_ring is a
# falsity witness for).  The capacity is ENGINE data -- the engine sizes
# its ring (hslots = next_pow2(max_delay+1), a power of two for the
# bit-mask addressing) and hands it to the law layer as a parameter, so
# the conjunct is a companion gate rather than a Config field (the
# config tree stays engine-agnostic; the JSON ingress constructs
# configs, not rings).  ok + ok_cap together accept exactly the
# configurations the proved backend may run: shape-correct routing
# over a ring that provably cannot alias the horizon.
def ok_cap(+c: Config, +cap: Nat) -> Bool:
  Nat.is_le(cfg_horizon(c), cap)

# the Q2 anti-alias read: an average over the w source samples ending at
# the delayed newest, as a window record.  Bounds laws are instance-level
# for now (see LAWS_router.window_instance).
type Win is Data:
  Win{lo: Nat, hi: Nat}

def win_lo(+w: Win) -> Nat:
  match w:
    case Win{lo, hi}:
      lo

def win_hi(+w: Win) -> Nat:
  match w:
    case Win{lo, hi}:
      hi

def route_window(+n: Nat, +d: Nat, +w: Nat) -> Win:
  Win{Nat.sub(n, Nat.add(d, w)), Nat.sub(n, d)}


# --------------------------------------------------------------------------
# CSR: the per-projection sparse connectome as a Nat data structure.  The
# template's per-EDGE idelays live here (Proj.d is the projection's max).
# csr_ok formalises the invariants nb_hybrid checks in prose
# (nb_hybrid.py:~1642: "horizon >= max(idelay) + 1 ... would alias two
# distinct delays onto the same buffer slot"):
#   * indptr starts at 0, is non-decreasing (row bounds are ordered);
#   * the last indptr entry equals the number of indices AND of delays
#     (every edge has both a source and a delay);
#   * every index is a valid source node;
#   * every per-edge delay fits the history horizon.
# --------------------------------------------------------------------------

type Csr is Data:
  Csr{indptr: List<&2, Nat>, indices: List<&2, Nat>, delays: List<&2, Nat>}

def csr_indptr(+c: Csr) -> List<&2, Nat>:
  match c:
    case Csr{indptr, indices, delays}:
      indptr

def csr_indices(+c: Csr) -> List<&2, Nat>:
  match c:
    case Csr{indptr, indices, delays}:
      indices

def csr_delays(+c: Csr) -> List<&2, Nat>:
  match c:
    case Csr{indptr, indices, delays}:
      delays

def nats_last_step(xs: List<&2, Nat>, prev: Nat) -> Nat:
  match xs:
    case Nil{}:
      prev
    case h <> t:
      nats_last_step(t, h)

def nats_last(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      nats_last_step(t, h)

def csr_fz_go(h: Nat) -> Bool:
  match h:
    case 0n:
      True{}
    case 1n+p:
      False{}

def csr_first_zero(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      csr_fz_go(h)


def csr_sorted_go(xs: List<&2, Nat>, prev: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(Nat.is_le(prev, h), csr_sorted_go(t, h))

def csr_sorted(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      csr_sorted_go(t, h)


def nats_lt_all(+b: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(Nat.is_lt(h, b), nats_lt_all(b, t))

def csr_ok(+nsrc: Nat, +horizon: Nat, +c: Csr) -> Bool:
  Bool.and(csr_first_zero(csr_indptr(c)),
  Bool.and(csr_sorted(csr_indptr(c)),
  Bool.and(Nat.is_eq(nats_last(csr_indptr(c)), nats_len(csr_indices(c))),
  Bool.and(Nat.is_eq(nats_len(csr_indices(c)), nats_len(csr_delays(c))),
  Bool.and(nats_lt_all(nsrc, csr_indices(c)),
           nats_lt_all(horizon, csr_delays(c)))))))

# nats_take: the first k elements of a Nat list (drop's mirror; k past
# the end yields the whole list -- the same saturating convention as
# hist_drop and nats_nth's default-past-end, so slices never fabricate
# elements).  With nats_drop this gives the CSR row slice.
def nats_take(xs: List<&2, Nat>, k: Nat) -> List<&2, Nat>:
  match xs k:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      Nil{}
    case h <> t 1n+q:
      h <> nats_take(t, q)

# nats_drop: the list past the first k elements, saturating like hist_drop
def nats_drop(xs: List<&2, Nat>, k: Nat) -> List<&2, Nat>:
  match xs k:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      xs
    case h <> t 1n+q:
      nats_drop(t, q)

# the CSR row slice: the elements of xs at indices [lo, hi) -- exactly
# the config's rows between indptr[t] and indptr[t+1] when xs is the
# edge array and (lo, hi) the row's bounds.
def nats_slice(xs: List<&2, Nat>, +lo: Nat, +hi: Nat) -> List<&2, Nat>:
  nats_take(nats_drop(xs, lo), Nat.sub(hi, lo))

# the row bounds of node t: (indptr[t], indptr[t+1]) with the same
# default-past-end convention as nats_nth (out-of-range indptr reads 0)
def csr_row_lo(+c: Csr, +t: Nat) -> Nat:
  nats_nth(csr_indptr(c), t)

def csr_row_hi(+c: Csr, +t: Nat) -> Nat:
  nats_nth(csr_indptr(c), Nat.add(t, 1n))

# the node t's row of the indices array: sources indptr[t]..indptr[t+1]
def csr_row_indices(+c: Csr, +t: Nat) -> List<&2, Nat>:
  nats_slice(csr_indices(c), csr_row_lo(c, t), csr_row_hi(c, t))

# the node t's row of the delays array: same bounds, same slice
def csr_row_delays(+c: Csr, +t: Nat) -> List<&2, Nat>:
  nats_slice(csr_delays(c), csr_row_lo(c, t), csr_row_hi(c, t))
# THE CAPSTONE COMPOSITION (Link 4): the routing table of target t's row.
# The engine's per-target gather folds w * blend(...) over the edges of
# the config's CSR row t; these defs are that row's LINES -- the routed
# read each edge consumes -- built in lockstep over the flat arrays so
# the (src, delay) pair can never desynchronize.
#
# An edge's routed line: read source lane s (indices[e]) at delay
# delays[e].  No Proj is fabricated -- the projection IS (src, d).
def edge(+ls: List<&2, Lane>, +s: Nat, +d: Nat) -> Line:
  route_read(lane_newest(nth_lane(ls, s)), d,
             lane_num(nth_lane(ls, s)), lane_k(nth_lane(ls, s)), 0n)

# the lines of cnt edges starting at flat index e0, in config order
# (the row's bounds under csr_ok; the pair (src, delay) is read at the
# SAME flat index, so it cannot desynchronize)
def edge_lines_from(+ls: List<&2, Lane>, +ixs: List<&2, Nat>,
                    +ds: List<&2, Nat>, +cnt: Nat, +e0: Nat)
  -> List<&2, Line>:
  match cnt:
    case 0n:
      Nil{}
    case 1n+q:
      edge(ls, nats_nth(ixs, e0), nats_nth(ds, e0))
        <> edge_lines_from(ls, ixs, ds, q, Nat.add(e0, 1n))

# the routing table of target t's row: the lines of exactly the
# indptr[t] .. indptr[t+1] edges, in config order
def csr_row_lines(+ls: List<&2, Lane>, +c: Csr, +t: Nat) -> List<&2, Line>:
  edge_lines_from(ls, csr_indices(c), csr_delays(c),
                  Nat.sub(csr_row_hi(c, t), csr_row_lo(c, t)), csr_row_lo(c, t))



# a lane is DUE (integrates and publishes this tick) iff its countdown
# has reached zero.  The kernel's `if t % k == 0` gate, carried.
def lane_due(+l: Lane) -> Bool:
  Nat.is_eq(lane_left(l), 0n)

# the countdown's next value depends ONLY on (left, k) -- never on the
# published count.  parity_audit decision 10's "identical step grids":
# two equal-k lanes stepped from init are the same pure function of t,
# so equal-k merge grids are exact by construction (purity), and left_det
# is the property a drifting C++/numba buffer would violate.
def left_next(left: Nat, +k: Nat) -> Nat:
  match left:
    case 0n:
      Nat.sub(k, 1n)
    case 1n+p:
      p

# --------------------------------------------------------------------------
# The decider-as-Type pattern (ordering/equality as propositions), kept for

# the witness-carrying constructor and the negative tests.
# --------------------------------------------------------------------------

def le_ok(+a: Nat, +b: Nat) -> Type:
  match a b:
    case 0n _:
      Unit
    case 1n+p 0n:
      Empty
    case 1n+p 1n+q:
      le_ok(p, q)

def lt_ok(+a: Nat, +b: Nat) -> Type:
  le_ok(Nat.add(a, 1n), b)

def le_refl(+x: Nat) -> le_ok(x, x):
  match x:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

# a read whose delay is PROVABLY inside the published history: the witness
# argument cannot be fabricated for d > n, so this constructor is uncallable
# on an out-of-history read (bad_router.bend tries, and fails)
def checked_read(+n: Nat, +d: Nat, +num: Nat, +den: Nat, +win: Nat,
                 -w: le_ok(d, n)) -> Line:
  route_read(n, d, num, den, win)
