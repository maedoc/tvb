# LAWS_coupling.bend -- STAGE-A claims for the COUPLING-TARGETING layer
# (COUPLING_LAWS_DESIGN.md, families C1 + C2 -- the PREREQS).  Every law
# here has its proof in PROOF_coupling.bend; the gate is
# tests/run_coupling.sh (verdict + the two cvar negatives + the smoke).
#
# The claim the whole plan closes -- "a contribution from a source cvar
# lands at the explicitly targeted (lane, tcvar) site and at no other
# site" -- is the C3/C4/C5 half (couple_all, untargeted-site, capstone)
# and does NOT live here (stages B/C).  This file pins the two
# PREREQS that make the source cvar load-bearing:
#
#   C1: the tape is INDEXED BY CVAR.  cvar_tape(tapes, L, v) is row
#       (L, v) of the cvar plane [lane][cvar][tick] -- cs_row re-used
#       verbatim at the cvar level, plane_row (the cs_row pattern one
#       level up) at the lane level, so every existing tape law applies
#       per row unchanged.
#
#   C2: the read is CVAR-SELECTIVE.  edge_cells_cvar reads the routed
#       window over the SOURCE cvar's tape (p.svar at lane p.src) -- the
#       cvar-aware range IS the plain section-9 range over that tape.
#       Mutate which cvar's tape the read names and the law refuses to
#       close: a wrong-but-in-range source cvar (the hole
#       bad/bad_cvar.bend leaves) is a law-level failure, not just an
#       mc_ok bounds pass.
#
# Law style follows LAWS_router.bend section 9 / LAWS_mconfig.bend:
# claims at the index/Bool level, floats as payload only; binders
# reused inside a claim carry `+` (Data only).
import Base
import ./coupling.bend as C
import ./mconfig.bend as M
import ./router.bend as R
import ./hist.bend as H

# --------------------------------------------------------------------------
# C1 -- the cvar-indexed tape plane
# --------------------------------------------------------------------------

# reading lane L's cvar-v tape IS reading plane row (L, v): the cvar
# plane is a list of tapes -- [lane][cvar][tick] -- and the cvar
# dimension is an INDEX, not a new memory theory (every tape law keeps
# applying per row).  cs_row is coupling.bend's own row projection,
# re-used verbatim for the inner (cvar) level.
law cvar_tape_nth:
  for +tapes: List<&2, List<&2, List<&2, F32>>>
  for +L: Nat
  for +v: Nat
  for +i: Nat
  for +ic: F32
  {H.hist_read(C.cvar_tape(tapes, L, v), i, ic)
     == H.hist_read(C.cs_row(C.plane_row(tapes, L), v), i, ic) : F32}

# the instance pin (the csr_ok_good convention: instance pins are
# load-bearing -- they pin the INTENDED reading): the 2-lane
# heterogeneous plane of the smoke -- lane 0 carries cvars y0/t1 and
# y1/t2 (JansenRit's 2 state variables), lane 1 carries xi/t3 (FHN's 1)
# -- and cvar_tape(tapes, 0n, 1n) IS 'y1's OWN tape t2.
law cvar_tape_instance:
  {C.cvar_tape(((1.0 <> 2.0 <> Nil{}) <> (3.0 <> 4.0 <> Nil{}) <> Nil{})
                 <> ((5.0 <> 6.0 <> Nil{}) <> Nil{}) <> Nil{},
               0n, 1n)
     == 3.0 <> 4.0 <> Nil{} : List<&2, F32>}

# --------------------------------------------------------------------------
# C2 -- the read is cvar-selective
# --------------------------------------------------------------------------

# the cvar-aware routed range IS the plain range (edge_cells, section
# 9) read over the SOURCE cvar's tape -- the projection's own cvar
# (p.svar) at the projection's own lane (p.src).  This is the law that
# makes svar load-bearing in the coupled read.  d/w (the plain window
# shape) ride as parameters: the M-view carries src/tgt/svar/tcvar
# only, and the window POSITION is the section-9 routing of the plain
# view Proj{src, tgt, d, w, tcvar} -- gone through UNCHANGED (the
# plain projection constructor is spelled out here because the M-view
# has no plain() bridge; the field order is Proj{src, tgt, d, win, tc}).
law edge_cells_cvar:
  for +ls: List<&2, R.Lane>
  for +p: M.MProj
  for +d: Nat
  for +w: Nat
  for +tapes: List<&2, List<&2, List<&2, F32>>>
  for +ic: F32
  {C.edge_cells_cvar(ls, p, d, w, tapes, ic)
     == C.edge_cells(ls,
                     R.Proj{M.mproj_src(p), M.mproj_tgt(p), d, w,
                            M.mproj_tcvar(p)},
                     C.cvar_tape(tapes, M.mproj_src(p), M.mproj_svar(p)),
                     ic)
   : List<&2, F32>}

# the instance pin: the 2-lane heterogeneous plane from the smoke
# (y0/y1 on lane 0, xi on lane 1), the cross-model projection
# MProj{0n, 1n, 1n, 0n} -- svar 1 ('y1') at source lane 0, tcvar 0
# ('xi') at target lane 1 -- with the routed window (d=1, w=2 at newest
# 3 -> (lo, hi] = ticks 1..2).  The window's cells ARE 'y1's tape's
# cells -- NOT any other cvar's: both bad controls (svar/tcvar swap and
# a wrong-but-in-range source cvar) change this reading.
law edge_cells_cvar_instance:
  {C.edge_cells_cvar(R.Lane{1n, 0n, 3n} <> Nil{},
                     M.MProj{0n, 1n, 1n, 0n}, 1n, 2n,
                     ((1.0 <> 2.0 <> 3.0 <> Nil{})
                        <> (10.0 <> 11.0 <> 12.0 <> Nil{})
                        <> Nil{})
                       <> ((20.0 <> 21.0 <> Nil{}) <> Nil{}) <> Nil{},
                     0.0)
     == 11.0 <> 12.0 <> Nil{} : List<&2, F32>}
