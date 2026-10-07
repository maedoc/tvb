# LAWS_mconfig.bend -- the claims for the CONFIG-COMPLEXITY layer
# (heterogeneous subnets: per-lane model cvar counts, model-relative
# projection cvars).  Every law here has its proof in PROOF_mconfig.bend;
# the gate is tests/run_mconfig.sh (verdict + the cvar negative control +
# the smoke).
#
# The spec is SWEEP_LAWS_DESIGN.md's final "Refresh 2026-10-05" section:
# subnets are heterogeneous MODELS (JansenRit vs ReducedSetFitzHughNagumo
# in the getting-started demo -- different state_variables, different
# cvar lists), and an InterProjection maps NAMED cvars across models, so
# a projection's coupling slot is MODEL-RELATIVE, resolved against each
# model's own cvar count.  The layer (mconfig.bend) adds that shape
# WITHOUT touching router.bend: a per-lane cvar-count list, a parallel
# MProj view built by mview, and the mc_ok validator whose four flat
# conjuncts are (a) shape coverage, (b)/(c) the model-relative cvar
# bounds, (d) the plain config's R.ok.
#
# Law style follows LAWS_router.bend sections 6/5b: the inversion family
# (mc_ok == True decomposes into the four conjuncts), the per-index
# forms (ok_proj_shape_nth analogs over the view), the pairing laws
# (the view's src/tgt agree with the plain config's projections, per
# index), instance pins, and the composition capstone mc_contract
# (cvar bounds + the routing contract, the sweep_contract pattern).
import Base
import ./mconfig.bend as M
import ./router.bend as R
import ./sweep.bend as S

# --------------------------------------------------------------------------
# the instances: the demo's shape, pinned
# --------------------------------------------------------------------------

# the getting-started heterogeneous network: cortex (JansenRit, cvar
# count 2) + thalamus (ReducedSetFitzHughNagumo, cvar count 1), one
# projection cortex -> thalamus at delay 0 (its InterProjection), the
# source cvar 'y1' resolved to index 0 of the 2, the target cvar 'xi'
# resolved to index 0 of the 1.
def GOOD_C() -> R.Config:
  R.Config{1n <> 1n <> Nil{}, R.Proj{0n, 1n, 0n, 0n, 0n} <> Nil{}, 1n}

def GOOD_SHAPES() -> List<&2, Nat>:
  2n <> 1n <> Nil{}

def GOOD_MPS() -> List<&2, M.MProj>:
  M.mview(R.cfg_projs(GOOD_C()), 0n <> Nil{}, 0n <> Nil{})

# the negative shape: the SAME network with the target cvar 'xi'
# resolved to index 1 of a 1-cvar model -- out of range, exactly the
# named-cvar typo the validator exists to catch.
def BAD_MPS() -> List<&2, M.MProj>:
  M.mview(R.cfg_projs(GOOD_C()), 0n <> Nil{}, 1n <> Nil{})

# --------------------------------------------------------------------------
# the instance pins (the csr_ok_good convention: positive/negative
# instance laws are load-bearing -- they pin the INTENDED reading)
# --------------------------------------------------------------------------

# the demo's heterogeneous config is ACCEPTED: different cvar counts
# (2 and 1), one cross-model projection at cvar (0, 0), both in range.
law mc_ok_good:
  {M.mc_ok(GOOD_SHAPES(), GOOD_MPS(), GOOD_C()) == True{} : Bool}

# the negative instance: the target cvar index 1 exceeds the target
# model's cvar count 1 -- REJECTED.
law mc_ok_bad_cvar:
  {M.mc_ok(GOOD_SHAPES(), BAD_MPS(), GOOD_C()) == False{} : Bool}

# --------------------------------------------------------------------------
# the inversion family (the section-6 and-elim pattern): mc_ok == True
# decomposes into its four conjuncts.  The binary dies on False, so the
# interesting heterogeneous facts are CONDITIONAL on acceptance.
# --------------------------------------------------------------------------

# (a) the shape list covers exactly the lanes
law mc_ok_shape:
  for +shapes: List<&2, Nat>
  for +mps: List<&2, M.MProj>
  for +c: R.Config
  for +h: {M.mc_ok(shapes, mps, c) == True{} : Bool}
  {Nat.is_eq(R.nats_len(shapes), R.nats_len(R.cfg_lanes(c))) == True{} : Bool}

# (b) the source-cvar fold: every view row's source cvar is inside its
# source lane's model cvar count
law mc_ok_src_cvar:
  for +shapes: List<&2, Nat>
  for +mps: List<&2, M.MProj>
  for +c: R.Config
  for +h: {M.mc_ok(shapes, mps, c) == True{} : Bool}
  {M.mprojs_src_ok(shapes, mps) == True{} : Bool}

# (c) the target-cvar fold: every view row's target cvar is inside its
# target lane's model cvar count
law mc_ok_tgt_cvar:
  for +shapes: List<&2, Nat>
  for +mps: List<&2, M.MProj>
  for +c: R.Config
  for +h: {M.mc_ok(shapes, mps, c) == True{} : Bool}
  {M.mprojs_tgt_ok(shapes, mps) == True{} : Bool}

# (d) the base gate: the plain config passes the router's own ok
law mc_ok_base:
  for +shapes: List<&2, Nat>
  for +mps: List<&2, M.MProj>
  for +c: R.Config
  for +h: {M.mc_ok(shapes, mps, c) == True{} : Bool}
  {R.ok(c) == True{} : Bool}

# --------------------------------------------------------------------------
# the per-index forms (the ok_proj_shape_nth analog): every accepted
# projection's cvars are in range, BY INDEX
# --------------------------------------------------------------------------

# the source-cvar bound at index i (in bounds): the fold is not just
# true of the fold -- every reachable view row passes its validator.
law mc_src_nth:
  for +shapes: List<&2, Nat>
  for +mps: List<&2, M.MProj>
  for i: Nat
  for h: R.lt_ok(i, M.mprojs_len(mps))
  for hok: {M.mprojs_src_ok(shapes, mps) == True{} : Bool}
  {M.mproj_src_ok(shapes, M.nth_mproj(mps, i)) == True{} : Bool}

# the target-cvar bound at index i (in bounds)
law mc_tgt_nth:
  for +shapes: List<&2, Nat>
  for +mps: List<&2, M.MProj>
  for i: Nat
  for h: R.lt_ok(i, M.mprojs_len(mps))
  for hok: {M.mprojs_tgt_ok(shapes, mps) == True{} : Bool}
  {M.mproj_tgt_ok(shapes, M.nth_mproj(mps, i)) == True{} : Bool}

# --------------------------------------------------------------------------
# the pairing laws: the cvar view agrees with the plain config's
# projections, per index -- mview copies src/tgt faithfully, one view
# row per projection (so a view index IS a projection index)
# --------------------------------------------------------------------------

# view completeness: mview produces exactly one MProj per projection
law mview_len:
  for +ps: List<&2, R.Proj>
  for +svs: List<&2, Nat>
  for +tvs: List<&2, Nat>
  {M.mprojs_len(M.mview(ps, svs, tvs)) == R.projs_len(ps) : Nat}

# the source pairing: view row i's src IS projection i's src
law mview_src_nth:
  for +ps: List<&2, R.Proj>
  for +svs: List<&2, Nat>
  for +tvs: List<&2, Nat>
  for i: Nat
  for h: R.lt_ok(i, R.projs_len(ps))
  {M.mproj_src(M.nth_mproj(M.mview(ps, svs, tvs), i))
     == R.proj_src(R.nth_proj(ps, i)) : Nat}

# the target pairing: view row i's tgt IS projection i's tgt
law mview_tgt_nth:
  for +ps: List<&2, R.Proj>
  for +svs: List<&2, Nat>
  for +tvs: List<&2, Nat>
  for i: Nat
  for h: R.lt_ok(i, R.projs_len(ps))
  {M.mproj_tgt(M.nth_mproj(M.mview(ps, svs, tvs), i))
     == R.proj_tgt(R.nth_proj(ps, i)) : Nat}

# --------------------------------------------------------------------------
# THE CAPSTONE: the cvar bounds compose with the routing contract (the
# sweep_contract pattern).  For a config whose view passes mc_ok, an
# in-bounds projection index i carries BOTH halves at once:
#   (a) the model-relative cvar bounds hold at view row i (the pair of
#       per-index validators);
#   (b) the router's full routing contract holds at projection i --
#       fresh, in-window, ordered (the bridge routing_contract_at in
#       PROOF_router.bend discharges it, exactly as sweep_contract's
#       third conjunct is discharged).
# The view is taken at mview(cfg_projs(c), svs, tvs) DEFINITIONALLY (no
# tie hypothesis needed); the index witness is stated in BOOL form
# ({is_le(1n+i, |projs|) == True}, the le_ok_iff bridge's Bool half)
# because TWO independent consumers need it (the view transport and the
# routing contract) and a Type-valued lt_ok witness cannot be
# duplicated -- each consumer rebuilds its own witness from the Bool
# form with PR.b_le.
law mc_contract:
  for +shapes: List<&2, Nat>
  for +svs: List<&2, Nat>
  for +tvs: List<&2, Nat>
  for +c: R.Config
  for +t: Nat
  for +i: Nat
  for +h: {M.mc_ok(shapes, M.mview(R.cfg_projs(c), svs, tvs), c) == True{} : Bool}
  for +hib: {Nat.is_le(Nat.add(i, 1n), R.projs_len(R.cfg_projs(c))) == True{} : Bool}
  {(M.mproj_src_ok(shapes, M.nth_mproj(M.mview(R.cfg_projs(c), svs, tvs), i)),
    M.mproj_tgt_ok(shapes, M.nth_mproj(M.mview(R.cfg_projs(c), svs, tvs), i)),
    S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), t, i))
   ==
   (True{}, True{}, True{})
   : Bool & (Bool & Bool)}
