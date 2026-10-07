# coupling.bend -- the average's WIRING, Link 5 of the ladder: which
# floats go into the average, and where the result enters.
#
# The router routes INDICES (Line/Win); kernel.bend turns pairs into
# values (blend/gather/f32_average).  This file is the bridge the user
# asked to make provable -- the ROUTING of the average, in two halves:
#
#   1. the RANGE: win_cells picks the exact float range fed to
#      f32_average, and the laws pin that the range matches the routed
#      window -- exactly hi - lo == w samples (window_span), at exactly
#      the routed indices (win_cells_nth + edge_cells_nth).
#   2. the SITE: the averaged value enters the coupling state at
#      (proj_tgt, proj_tc) -- the correct cvar slot (tc) of the correct
#      node/lane (tgt) -- and at no other site (cs_set_stable_*).
#
# WINDOW READING -- the (lo, hi] convention, pinned by win_cells_instance:
# route_window(n, d, w) = Win{lo, hi} with lo = n-(d+w), hi = n-d and
# hi - lo == w (window_span).  The w samples of the average are the ticks
# lo+1 .. hi INCLUSIVE -- the window covers (lo, hi] -- so the average
# ENDS AT hi = n-d (the point the interpolation reads first,
# read_i0_is_window_head) and its OLDEST member is lo+1 = n-d-w+1, age
# d+w-1 (the window_head_age prose's "d+k-1 ticks old" reading).  The
# instance law pins this reading against the day-one window_instance
# Win{5, 8} (w=3 -> ticks 6, 7, 8).
#
# CS READING -- the coupling state is the c[var][j] plane of the engine
# (mcore.bend's "c[var][j] += wsum"), modelled as rows (one per
# node/lane, the tgt index) of F32 columns (one per cvar slot, the tc
# index).  cs_add accumulates at exactly one (row, column) site -- the
# "+=" of the template -- and the read-after-write / stability laws are
# the state-level soundness of that write.
import Base
import ./router.bend as R
import ./kernel.bend as K
import ./hist.bend as H
import ./mconfig.bend as M

# --------------------------------------------------------------------------
# the range: the exact floats fed to the average
# --------------------------------------------------------------------------

# exactly w tape samples at ticks lo+1 .. lo+w -- the (lo, lo+w] window.
# Built oldest-first (the head is tick lo+1), matching the template's
# ascending += fold order.  Reads past the tape's end answer the IC fill
# (hist_read's default-past-end), so the range has EXACTLY w entries for
# any tape -- short histories give the IC-padded window, never a short
# range.  (No forward refs; w is the shrinking argument.)
def win_cells_go(w: Nat, +tape: List<&2, F32>, +lo: Nat, +ic: F32) -> List<&2, F32>:
  match w:
    case 0n:
      Nil{}
    case 1n+s:
      H.hist_read(tape, 1n+lo, ic) <> win_cells_go(s, tape, 1n+lo, ic)

# (call sites keep the (tape, lo, w, ic) order -- w leads the go so the
# DECREASING argument comes first, Bend's termination rule)
def win_cells(+tape: List<&2, F32>, +lo: Nat, w: Nat, +ic: F32) -> List<&2, F32>:
  win_cells_go(w, tape, lo, ic)

# the routed window's cells: projection p's average window against the
# SOURCE lane's tape, positioned at route_window(newest, d, win).lo with
# exactly proj_win(p) samples -- the range edge_write feeds f32_average.
def edge_cells(+ls: List<&2, R.Lane>, +p: R.Proj,
               +tape: List<&2, F32>, +ic: F32) -> List<&2, F32>:
  win_cells(tape,
            R.win_lo(R.route_window(R.lane_newest(R.nth_lane(ls, R.proj_src(p))),
                                   R.proj_d(p), R.proj_win(p))),
            R.proj_win(p), ic)

# one coupling write: the averaged value with its destination site.
# (tgt, tc) is (node/lane, cvar slot) -- the site writes_unique and
# ok_no_clash police at the config level.
type Write is Data:
  Write{w_tgt: Nat, w_tc: Nat, w_val: F32}

def w_tgt(+w: Write) -> Nat:
  match w:
    case Write{w_tgt, w_tc, w_val}:
      w_tgt

def w_tc(+w: Write) -> Nat:
  match w:
    case Write{w_tgt, w_tc, w_val}:
      w_tc

def w_val(+w: Write) -> F32:
  match w:
    case Write{w_tgt, w_tc, w_val}:
      w_val

# the per-projection coupling write at one tick: average the routed
# window's cells and address the result to (proj_tgt, proj_tc).  den/acc
# are the caller's divisor and zero (the kernel's accumulator contract,
# same as gather's acc).
def edge_write(+ls: List<&2, R.Lane>, +p: R.Proj,
               +tape: List<&2, F32>, +ic: F32, +den: F32, +acc: F32) -> Write:
  Write{R.proj_tgt(p), R.proj_tc(p),
        K.f32_average(edge_cells(ls, p, tape, ic), den, acc)}

# --------------------------------------------------------------------------
# the site: the coupling state c[node][cvar] and its "+="
# --------------------------------------------------------------------------

# the tgt-th row of the state (the node/lane's cvar row); missing rows
# read as the empty row
def cs_row(cs: List<&2, List<&2, F32>>, tgt: Nat) -> List<&2, F32>:
  match cs tgt:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      h
    case h <> t 1n+p:
      cs_row(t, p)

# read one cvar slot of one row; past-the-end answers the caller's zero
# (the accumulate identity), the hist_read default convention
def cs_get_row(r: List<&2, F32>, tc: Nat, +zero: F32) -> F32:
  match r tc:
    case Nil{} _:
      zero
    case h <> t 0n:
      h
    case h <> t 1n+p:
      cs_get_row(t, p, zero)

def cs_get(cs: List<&2, List<&2, F32>>, tgt: Nat, tc: Nat,
           +zero: F32) -> F32:
  cs_get_row(cs_row(cs, tgt), tc, zero)

# write one cvar slot of one row; extension fills gaps with the
# accumulator's zero (so the write always LANDS at its slot -- unlike
# ring_write's tick-order extension, here the caller may skip indices)
def cs_set_row(r: List<&2, F32>, s: Nat, +v: F32, +zero: F32) -> List<&2, F32>:
  match r s:
    case Nil{} 0n:
      v <> Nil{}
    case Nil{} 1n+p:
      zero <> cs_set_row(Nil{}, p, v, zero)
    case h <> t 0n:
      v <> t
    case h <> t 1n+p:
      h <> cs_set_row(t, p, v, zero)

# write one (node, cvar) site of the state; missing rows are created
# (empty, zero-filled on write) the same way
def cs_set(cs: List<&2, List<&2, F32>>, tgt: Nat, s: Nat,
           +v: F32, +zero: F32) -> List<&2, List<&2, F32>>:
  match cs tgt:
    case Nil{} 0n:
      cs_set_row(Nil{}, s, v, zero) <> Nil{}
    case Nil{} 1n+p:
      Nil{} <> cs_set(Nil{}, p, s, v, zero)
    case h <> t 0n:
      cs_set_row(h, s, v, zero) <> t
    case h <> t 1n+p:
      h <> cs_set(t, p, s, v, zero)

# the template's "c[var][j] += wsum": accumulate v at exactly one site
def cs_add(+cs: List<&2, List<&2, F32>>, +tgt: Nat, +tc: Nat,
           +v: F32, +zero: F32) -> List<&2, List<&2, F32>>:
  cs_set(cs, tgt, tc, F32.add(cs_get(cs, tgt, tc, zero), v), zero)

# --------------------------------------------------------------------------
# THE CVAR PLANE (COUPLING_LAWS_DESIGN.md families C1/C2 -- the stage-A
# PREREQS, next law family): the tape becomes [lane][cvar][tick], so the
# read names the cvar.  The plane is a plain list of per-lane cvar-tape
# lists, so every existing tape law applies PER ROW unchanged -- no new
# memory theory, just an index.  Row machinery: cs_row is re-used
# VERBATIM for the inner (cvar) level; plane_row is the same pattern one
# level up (the outer list's element type differs, so the def is spelled
# out -- the doc's "reuse cs_row verbatim, the tape plane is the same
# shape").  The write side of the plane (which cvar's tape an edge_write
# addresses) is stage B/C; this section pins the READ only.
# --------------------------------------------------------------------------

# the L-th lane's cvar list (the cs_row pattern at the plane level;
# missing lanes read as the empty cvar list, the nats_nth convention)
def plane_row(tapes: List<&2, List<&2, List<&2, F32>>>, tgt: Nat)
    -> List<&2, List<&2, F32>>:
  match tapes tgt:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      h
    case h <> t 1n+p:
      plane_row(t, p)

# the v-th cvar tape of lane L: row (L, v) of the plane (cs_row re-used
# verbatim at the cvar level; missing cvars read the empty tape)
def cvar_tape(tapes: List<&2, List<&2, List<&2, F32>>>, L: Nat, v: Nat)
    -> List<&2, F32>:
  cs_row(plane_row(tapes, L), v)

# the cvar-SELECTIVE routed read (C2): the routed window against the
# SOURCE cvar's tape -- p.svar at lane p.src.  The window POSITION is
# exactly edge_cells' section-9 routing (route_window at the source
# lane's newest, width w); d/w ride as parameters because the M-view
# (mconfig.bend) carries src/tgt/svar/tcvar only -- the cvar axis is
# what this function adds, the routing shape is re-used, not re-derived.
def edge_cells_cvar(+ls: List<&2, R.Lane>, +p: M.MProj, +d: Nat, +w: Nat,
                    +tapes: List<&2, List<&2, List<&2, F32>>>, +ic: F32)
    -> List<&2, F32>:
  win_cells(cvar_tape(tapes, M.mproj_src(p), M.mproj_svar(p)),
            R.win_lo(R.route_window(R.lane_newest(R.nth_lane(ls, M.mproj_src(p))),
                                    d, w)),
            w, ic)
