# PROOF_coupling.bend -- the proofs for LAWS_coupling.bend (stage A:
# families C1 + C2 of COUPLING_LAWS_DESIGN.md).  The gate:
#
#   bend PROOF_coupling.bend            must print ALL PROOFS CHECK
#   bend PROOF_coupling.bend --verdict  re-checked by the Lean-proved kernel
#
# All four fills are definitional: cvar_tape IS
# cs_row(plane_row(tapes, L), v) (C1), and edge_cells_cvar IS
# edge_cells at the plain view Proj{src, tgt, d, w, tcvar} over that
# same cvar-selected tape (C2) -- after normalisation both sides of
# each claim are the same win_cells / hist_read term, so each closes
# with {==}.
import Base
import ./LAWS_coupling.bend as Laws
import ./coupling.bend as C
import ./mconfig.bend as M
import ./router.bend as R
import ./hist.bend as H

# --------------------------------------------------------------------------
# C1 -- the cvar-indexed tape plane
# --------------------------------------------------------------------------

def Laws.cvar_tape_nth(tapes, L, v, i, ic):
  {==}

def Laws.cvar_tape_instance():
  {==}

# --------------------------------------------------------------------------
# C2 -- the read is cvar-selective
# --------------------------------------------------------------------------

def Laws.edge_cells_cvar(ls, p, d, w, tapes, ic):
  {==}

def Laws.edge_cells_cvar_instance():
  {==}
