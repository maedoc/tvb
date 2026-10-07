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
import ./json_ingest.bend as J

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

# --------------------------------------------------------------------------
# P3a -- the PER-LANE SCHEME layer (SWEEP_LAWS_DESIGN.md, priority P3):
# the config gains a per-lane SCHEME id -- which integrator each subnet
# runs.  The scheme table is a `List<&2, Nat>` whose length is the number
# of available schemes; the per-lane assignment rides alongside shapes
# (the representation choice is documented in mconfig.bend).  The law
# family mirrors mc_ok's own: the per-lane bounds fold + its per-index
# form (the mc_src_nth pattern), the validator's and-elimination family,
# the routing law (lane i runs the table entry its id points at -- for
# the pinned identity assignment, lane i runs scheme i), and the
# instance pins.
# --------------------------------------------------------------------------

# the instance's scheme table: TWO schemes available (ids 0 and 1), and
# the pinned 2-lane assignment: lane 0 -> scheme 0, lane 1 -> scheme 1
# (the identity assignment -- lane i runs scheme i).
def SCHEME_TABLE() -> List<&2, Nat>:
  0n <> 1n <> Nil{}

def SCHEME_IDS() -> List<&2, Nat>:
  0n <> 1n <> Nil{}

# the negative assignment: lane 1's id 2 indexes PAST the 2-entry table --
# exactly the out-of-range integrator id the validator exists to catch.
def BAD_SCHEMES() -> List<&2, Nat>:
  0n <> 2n <> Nil{}

# the positive pin: the demo's heterogeneous network with the identity
# scheme assignment is ACCEPTED -- one id per lane, both ids inside the
# 2-entry table, the base mc_ok green.
law scheme_ok_good:
  {M.scheme_ok(SCHEME_TABLE(), SCHEME_IDS(), GOOD_SHAPES(), GOOD_MPS(),
               GOOD_C()) == True{} : Bool}

# the negative pin: lane 1's scheme id 2 is past the table -- REJECTED.
law scheme_ok_bad:
  {M.scheme_ok(SCHEME_TABLE(), BAD_SCHEMES(), GOOD_SHAPES(), GOOD_MPS(),
               GOOD_C()) == False{} : Bool}

# --------------------------------------------------------------------------
# the inversion family (the section-6 and-elim pattern): scheme_ok ==
# True decomposes into its three conjuncts.
# --------------------------------------------------------------------------

# (a) one scheme id per lane
law scheme_ok_len:
  for +table: List<&2, Nat>
  for +schemes: List<&2, Nat>
  for +shapes: List<&2, Nat>
  for +mps: List<&2, M.MProj>
  for +c: R.Config
  for +h: {M.scheme_ok(table, schemes, shapes, mps, c) == True{} : Bool}
  {Nat.is_eq(R.nats_len(schemes), R.nats_len(R.cfg_lanes(c))) == True{} : Bool}

# (b) the bounds fold: every lane's scheme id is inside the table
law scheme_ok_bounds:
  for +table: List<&2, Nat>
  for +schemes: List<&2, Nat>
  for +shapes: List<&2, Nat>
  for +mps: List<&2, M.MProj>
  for +c: R.Config
  for +h: {M.scheme_ok(table, schemes, shapes, mps, c) == True{} : Bool}
  {M.schemes_ok(schemes, R.nats_len(table)) == True{} : Bool}

# (c) the base gate: the heterogeneous layer's own validator
law scheme_ok_base:
  for +table: List<&2, Nat>
  for +schemes: List<&2, Nat>
  for +shapes: List<&2, Nat>
  for +mps: List<&2, M.MProj>
  for +c: R.Config
  for +h: {M.scheme_ok(table, schemes, shapes, mps, c) == True{} : Bool}
  {M.mc_ok(shapes, mps, c) == True{} : Bool}

# --------------------------------------------------------------------------
# the per-lane bounds, BY INDEX (the mc_src_nth pattern): every lane's
# scheme id is inside the scheme table -- not just true of the fold, but
# of every reachable lane.  The bounds witness is load-bearing: past the
# assignment list the read defaults to 0n and the claim would overreach.
# --------------------------------------------------------------------------

law scheme_bounded:
  for +schemes: List<&2, Nat>
  for +ntab: Nat
  for i: Nat
  for h: R.lt_ok(i, R.nats_len(schemes))
  for hok: {M.schemes_ok(schemes, ntab) == True{} : Bool}
  {Nat.is_lt(R.nats_nth(schemes, i), ntab) == True{} : Bool}

# --------------------------------------------------------------------------
# the routing law: lane i's RESOLVED scheme is the table entry its id
# points at.  When lane i's id IS i (the identity assignment -- the shape
# the instance pins), lane i runs scheme-table entry i: lane i runs
# scheme i.
# --------------------------------------------------------------------------

law scheme_nth:
  for +table: List<&2, Nat>
  for +schemes: List<&2, Nat>
  for +i: Nat
  for +hid: {M.lane_scheme(schemes, i) == i : Nat}
  {M.scheme_of(table, schemes, i) == R.nats_nth(table, i) : Nat}

# the instance pins: for the pinned 2-lane identity assignment, lane 0
# runs scheme-table entry 0 and lane 1 runs entry 1 -- literal
# computation (the csr_row_good convention).
law scheme_nth_inst_0:
  {M.scheme_of(SCHEME_TABLE(), SCHEME_IDS(), 0n) == 0n : Nat}

law scheme_nth_inst_1:
  {M.scheme_of(SCHEME_TABLE(), SCHEME_IDS(), 1n) == 1n : Nat}

# --------------------------------------------------------------------------
# P4 -- CVAR NAME-RESOLUTION (SWEEP_LAWS_DESIGN.md, priority P4): the
# association-list lookup family.  A model description carries its
# state-variable NAME LIST (List<&2, String>); find_name resolves a cvar
# NAME to its index -- the first occurrence -- with an unknown name
# landing on the junk index (the list's length, so the mc_ok bounds
# check rejects it).  The named projection: source/target cvar NAMES
# resolving against the SOURCE/TARGET models' name lists (per-model:
# the same name resolves differently in two models).  Laws: the found
# lookup (presence witnessed by a bounded index + the not_before
# first-occurrence fold), the unknown lookup (the sw_name_slot_unknown
# mirror), the pairing law (the resolved index IS the view's index),
# the bounded composition (a named projection that resolves is valid),
# and the instance pins.
# --------------------------------------------------------------------------

# the demo's two models, pinned: JansenRit's 6 state variables and
# ReducedSetFitzHughNagumo's 4 ('xi' is its FIRST state variable -- the
# demo's target_cvar slot [0]).
def JR_NAMES() -> List<&2, String>:
  "y0" <> "y1" <> "y2" <> "y3" <> "y4" <> "y5" <> Nil{}

def FHN_NAMES() -> List<&2, String>:
  "xi" <> "eta" <> "alpha" <> "beta" <> Nil{}

def MODELS() -> List<&2, List<&2, String>>:
  JR_NAMES() <> FHN_NAMES() <> Nil{}

# the demo's named projection: cortex -> thalamus, source cvar 'y1'
# (JansenRit), target cvar 'xi' (FHN).
def NPROJ_GOOD() -> M.NProj:
  M.NProj{0n, 1n, "y1", "xi"}

# the named layer's shapes: cvar bounds against the STATE-VARIABLE counts
# (6 and 4 -- the name lists' lengths; the name resolves to an index into
# the state variables, so that is the plane the bound guards)
def NAMED_SHAPES() -> List<&2, Nat>:
  6n <> 4n <> Nil{}

# the FOUND lookup: a name PRESENT at bounded index k (presence in Bool
# form -- {String.eq(str_nth(names, k), name) == True}, the Bool-form
# hypothesis pattern, since symbolic String equality has no decider) and
# FIRST at k (the not_before fold) resolves to exactly k.
law cvar_resolve_found:
  for +names: List<&2, String>
  for +name: String
  for k: Nat
  for +hpos: {String.eq(S.str_nth(names, k), name) == True{} : Bool}
  for +hfresh: {M.not_before(names, name, k) == True{} : Bool}
  for h: R.lt_ok(k, M.snames_len(names))
  {M.find_name(names, name) == k : Nat}

# the UNKNOWN lookup (the sw_name_slot_unknown mirror): a name the list
# does not contain resolves to the junk index -- the list's OWN length,
# computed, one past every valid slot.
law cvar_resolve_unknown:
  for +names: List<&2, String>
  for +name: String
  for +habs: {M.not_in(names, name) == True{} : Bool}
  {M.find_name(names, name) == M.snames_len(names) : Nat}

# one view row per named projection (the mview_len analog)
law mnview_len:
  for +nps: List<&2, M.NProj>
  for +ms: List<&2, List<&2, String>>
  {M.mprojs_len(M.mnview(nps, ms)) == M.nprojs_len(nps) : Nat}

# THE PAIRING LAW: a named projection's RESOLVED indices ARE its view
# row's svar/tcvar -- the view row i built by mnview carries exactly the
# name resolution of named projection i (per side: svar against the
# SOURCE lane's list, tcvar against the TARGET lane's).  The index
# witness rides in Bool form ({is_le(1n+i, |nps|) == True}) because TWO
# independent consumers (the svar and tcvar halves) each rebuild their
# own Type witness with PR.b_le.
law cvar_resolve_proj:
  for +nps: List<&2, M.NProj>
  for +ms: List<&2, List<&2, String>>
  for +i: Nat
  for +hib: {Nat.is_le(Nat.add(i, 1n), M.nprojs_len(nps)) == True{} : Bool}
  {(M.mproj_svar(M.nth_mproj(M.mnview(nps, ms), i)),
    M.mproj_tcvar(M.nth_mproj(M.mnview(nps, ms), i)))
   ==
   (M.find_name(M.nth_snames(ms, M.mproj_src(M.nth_mproj(M.mnview(nps, ms), i))),
                M.nproj_sname(M.nth_nproj(nps, i))),
    M.find_name(M.nth_snames(ms, M.mproj_tgt(M.nth_mproj(M.mnview(nps, ms), i))),
                M.nproj_tname(M.nth_nproj(nps, i))))
   : Nat & Nat}

# THE BOUNDED COMPOSITION: for a named config whose resolved view passes
# mc_ok, the resolved cvar index is IN RANGE of the model's cvar count --
# cvar_resolve_proj's pairing composed with the mc_ok source bounds (a
# named projection that resolves is valid).  The junk convention is what
# makes this honest: an unknown name's junk index (= the name list's
# length) fails the bound, so it cannot sneak through here.
law cvar_resolve_bounded:
  for +nps: List<&2, M.NProj>
  for +ms: List<&2, List<&2, String>>
  for +shapes: List<&2, Nat>
  for +c: R.Config
  for +i: Nat
  for +hib: {Nat.is_le(Nat.add(i, 1n), M.nprojs_len(nps)) == True{} : Bool}
  for +hok: {M.mc_ok(shapes, M.mnview(nps, ms), c) == True{} : Bool}
  {Nat.is_lt(M.find_name(M.nth_snames(ms, M.mproj_src(M.nth_mproj(M.mnview(nps, ms), i))),
                         M.nproj_sname(M.nth_nproj(nps, i))),
             R.nats_nth(shapes, M.mproj_src(M.nth_mproj(M.mnview(nps, ms), i))))
    == True{} : Bool}

# the instance pins (the csr_row_good convention).

# JansenRit-shaped: 'y1' resolves to index 1 of ["y0".."y5"] -- the
# demo's source_cvar.
law cvar_resolve_instance_jr:
  {M.find_name(JR_NAMES(), "y1") == 1n : Nat}

# the heterogeneity point: the SAME name resolves PER MODEL -- 'xi' is
# FHN's state variable 0, and ABSENT from JansenRit's list, where it
# lands on the junk index (the list's length, 6).
law cvar_resolve_cross:
  {(M.find_name(JR_NAMES(), "xi"), M.find_name(FHN_NAMES(), "xi"))
     == (6n, 0n) : Nat & Nat}

# the demo's named config is ACCEPTED: the resolved view (svar 1, tcvar
# 0) passes the mc_ok cvar bounds against the state-variable counts.
law cvar_ok_good:
  {M.mc_ok(NAMED_SHAPES(), M.mnview(NPROJ_GOOD() <> Nil{}, MODELS()),
           GOOD_C()) == True{} : Bool}

# --------------------------------------------------------------------------
# P4b -- the NAMED-CONFIG JSON INGRESS (the config-side ingress composing
# the name-resolution layer): the schema is PARALLEL TOP-LEVEL arrays --
# the plain triple (lanes/projs/horizon) exactly as the config schema,
# plus svar_names (one NAME LIST per lane/model), proj_svars / proj_tcvars
# (one cvar NAME per projection).  The named projections are ASSEMBLED
# from the decode (J.jn_nprojs: projection i's src/tgt paired with the
# i-th names), the shapes are the name lists' lengths (J.jn_shapes), and
# the validator J.jn_good is mc_ok at the decoded triple -- the ingress
# GATES on the name-resolution layer, never re-states it.  The decode is
# TOTAL (garbage -> the empty named config), so the capstone quantifies
# over ALL strings, the json_read_fresh / json_sweep_contract shape.
# --------------------------------------------------------------------------

# the transcription pin (the csr_row_good / json_decode_instance
# convention): the demo's heterogeneous network as a literal named-config
# JSON decodes to exactly the pinned values -- the demo's name lists
# (MODELS), the demo's named projection (NPROJ_GOOD: cortex -> thalamus,
# 'y1' / 'xi'), the GOOD_C config, all six keys seen, parse-valid.
law json_named_instance:
  {J.json_named_decode("{\"lanes\":[1,2],\"projs\":[[0,1,1,0,0]],\"horizon\":4,\"svar_names\":[[\"y0\",\"y1\",\"y2\",\"y3\",\"y4\",\"y5\"],[\"xi\",\"eta\",\"alpha\",\"beta\"]],\"proj_svars\":[\"y1\"],\"proj_tcvars\":[\"xi\"]}")
     == J.JN{1n <> 2n <> Nil{}, R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{}, 4n,
             MODELS(), "y1" <> Nil{}, "xi" <> Nil{}, 6n, True{}}
   : J.JN}

# garbage decodes to the empty named config -- the total-decode pin (the
# json_decode_garbage / json_sweep_garbage convention): every list empty,
# horizon 0, nothing seen, not parse-valid.
law json_named_garbage:
  {J.json_named_decode("zz not json")
     == J.JN{Nil{}, Nil{}, 0n, Nil{}, Nil{}, Nil{}, 0n, False{}} : J.JN}

# the ASSEMBLY's length law: the assembled named-projection list has one
# NProj per PLAIN projection -- the zip consumes the projections, so
# shortening the name lists cannot lose a projection (a short list reads
# "" past its end instead, the junk-name path the validator rejects).
law jn_zip_len:
  for +ps: List<&2, R.Proj>
  for +svs: List<&2, String>
  for +tvs: List<&2, String>
  {M.nprojs_len(J.zip_nprojs(ps, svs, tvs)) == R.projs_len(ps) : Nat}

# THE RESOLVE LAW: the decoded named projection's cvars resolve THROUGH
# find_name to in-range indices -- cvar_resolve_bounded composed with the
# decode.  For every string s whose decoded named config VALIDATES
# (J.jn_good: the name-per-projection lengths, then mc_ok at the decoded
# shapes/view/config) and every in-bounds named-projection index i, BOTH
# resolved indices land inside their models' name-list lengths -- source
# AND target (the bounded composition stated per side; the junk-index
# convention is what makes it honest: an unknown name's junk index fails
# the bound, so it cannot sneak through).
law json_named_resolve:
  for +s: String
  for +i: Nat
  for +hib: {Nat.is_le(Nat.add(i, 1n),
                       M.nprojs_len(J.jn_nprojs(J.json_named_decode(s)))) == True{} : Bool}
  for +h: {J.jn_good(J.json_named_decode(s)) == True{} : Bool}
  {(Nat.is_lt(M.find_name(
                M.nth_snames(J.jn_snames(J.json_named_decode(s)),
                             M.mproj_src(M.nth_mproj(J.jn_view(J.json_named_decode(s)), i))),
                M.nproj_sname(M.nth_nproj(J.jn_nprojs(J.json_named_decode(s)), i))),
              R.nats_nth(J.jn_shapes(J.json_named_decode(s)),
                         M.mproj_src(M.nth_mproj(J.jn_view(J.json_named_decode(s)), i)))),
    Nat.is_lt(M.find_name(
                M.nth_snames(J.jn_snames(J.json_named_decode(s)),
                             M.mproj_tgt(M.nth_mproj(J.jn_view(J.json_named_decode(s)), i))),
                M.nproj_tname(M.nth_nproj(J.jn_nprojs(J.json_named_decode(s)), i))),
              R.nats_nth(J.jn_shapes(J.json_named_decode(s)),
                         M.mproj_tgt(M.nth_mproj(J.jn_view(J.json_named_decode(s)), i)))))
   == (True{}, True{}) : Bool & Bool}

# THE NAMED-CONFIG CONTRACT -- the ingress capstone (the
# routing_contract_at bridge pattern at the decoded config, the
# json_read_fresh analog at the heterogeneous level): for EVERY string s
# whose decoded named config validates, and every in-bounds named
# projection i, at ANY tick t:
#   (a)/(b) the resolved view row i's cvars are in range of their models'
#       name-list lengths (the per-index mc bounds at the DECODED view);
#   (c) the router's full routing contract holds at the decoded config's
#       projection i -- fresh, in-window, ordered (PR.routing_contract_at
#       discharges it at jn_cfg, exactly as mc_contract's third conjunct).
# The decoded triple rides definitionally: shapes = jn_shapes (the name
# lists' lengths), view = jn_view (mnview of the assembled named
# projections), config = jn_cfg.  Nothing escapes a validated runtime
# input: the name resolution lands in range AND the routing is clean.
law json_named_contract:
  for +s: String
  for +t: Nat
  for +i: Nat
  for +h: {J.jn_good(J.json_named_decode(s)) == True{} : Bool}
  for +hib: {Nat.is_le(Nat.add(i, 1n),
                       M.nprojs_len(J.jn_nprojs(J.json_named_decode(s)))) == True{} : Bool}
  {(M.mproj_src_ok(J.jn_shapes(J.json_named_decode(s)),
                   M.nth_mproj(J.jn_view(J.json_named_decode(s)), i)),
    M.mproj_tgt_ok(J.jn_shapes(J.json_named_decode(s)),
                   M.nth_mproj(J.jn_view(J.json_named_decode(s)), i)),
    S.routing_bundle(J.jn_cfg(J.json_named_decode(s)),
                     R.init_lanes(R.cfg_lanes(J.jn_cfg(J.json_named_decode(s)))),
                     R.cfg_projs(J.jn_cfg(J.json_named_decode(s))), t, i))
   == (True{}, True{}, True{})
   : Bool & (Bool & Bool)}

# --------------------------------------------------------------------------
# P6 -- the DELAY-UNIT layer (SWEEP_LAWS_DESIGN.md, gap inventory item 6):
# the ms -> source-step conversion and its rounding rule, pinned.
#
# THE ROUNDING RULE (one line): with both delays and dt carried as the
# suite's x1e6 scaled integers, source steps = round-half-even(ms/dt) --
# q + 1 iff 2r > dt, or 2r == dt with q odd, where (q, r) = divmod(ms, dt)
# -- the exact rational mirror of TVB's numpy.rint(delays/dt).
#
# Law style follows the family convention: concrete rounding-rule witnesses
# (the csr_ok_good type: positive instance pins are load-bearing), the
# quantified monotonicity law (the causation guard: ms1 <= ms2 must never
# shift the converted read EARLIER), the per-tick non-decrease form, the
# strict "where the range allows" law (a boundary tick provably ADDS its
# step), and the validator's green/red instance pins.  Witness magnitudes
# are kept modest: the machine's cost is linear in the scaled ms value.
# --------------------------------------------------------------------------

# the demo's delays: dt 0.1 ms per lane (100000), one projection whose
# coupling delay is 0.2 ms (200000) -> round(2.0) = 2 source steps
def GOOD_DTS() -> List<&2, Nat>:
  100n <> 100n <> Nil{}

def GOOD_MSDS() -> List<&2, Nat>:
  200n <> Nil{}

# the sub-step delay: 0.04 ms at dt 0.1 ms -> round(0.4) = 0 steps, the
# nonzero delay that must be REJECTED by the validator
# (witnesses are x 1e-3 of the nominal x1e6-scaled values; the rules
# pin RATIOS exactly, and the countdown machine's per-tick cost is
# linear in the scaled ms, so instances stay small to fit the
# kernel-side verdict reduction budgets)
def SUBSTEP_MSDS() -> List<&2, Nat>:
  40n <> Nil{}

# --------------------------------------------------------------------------
# the rounding rule on concrete witnesses (a)/(c) of the family spec:
# --------------------------------------------------------------------------

# the exact-division case: 0.2 ms at dt 0.1 ms is 2.0 ratios -> 2 steps
law mdelay_exact:
  {M.ms_to_steps(200n, 100n) == 2n : Nat}

# the TIE witness: 0.05 ms at dt 0.1 ms is exactly 0.5 ratios, and
# half-to-even rounds the EVEN quotient down -> 0 steps (round-half-UP
# would give 1; the rule is pinned as the reference's rint, not half-up)
law mdelay_tie:
  {M.ms_to_steps(50n, 100n) == 0n : Nat}

# a FRACTIONAL, non-tie rounding witness: 0.75 ms at dt 0.1 ms rounds
# up to 1 step (floor is 0, ceiling is 1, and the rule must answer 1)
law mdelay_round_frac:
  {M.ms_to_steps(75n, 100n) == 1n : Nat}

# the OFF-BY-ROUNDING witness: 0.15 ms at dt 0.1 ms is exactly 1.5
# ratios, the ODD quotient rounds up -> 2 steps (truncation would give 1:
# one source step of causality silently lost -- exactly the gap item's
# "off-by-rounding shifts causality")
law mdelay_round_up:
  {M.ms_to_steps(150n, 100n) == 2n : Nat}

# the sub-step pin (the guard's premise): 0.04 ms at dt 0.1 ms -> 0 steps
law mdelay_substep:
  {M.ms_to_steps(40n, 100n) == 0n : Nat}

# real TVB-ish values (c): dt 0.1 ms -> a 0.3 ms delay is exactly 3 steps
law mdelay_tvb_dt01:
  {M.ms_to_steps(300n, 100n) == 3n : Nat}

# real TVB-ish values (c): dt 0.5 ms -> a 0.5 ms delay is exactly 1 step
law mdelay_tvb_dt05:
  {M.ms_to_steps(500n, 500n) == 1n : Nat}

# the strict-lattice instance (delay_injective's spirit, in instance form):
# two exact-step delays convert to DISTINCT steps -- monotone and injective
# on the step lattice
law mdelay_lattice:
  {Nat.is_ne(M.ms_to_steps(100n, 100n),
             M.ms_to_steps(200n, 100n)) == True{} : Bool}

# --------------------------------------------------------------------------
# the quantified family (b): monotonicity.  ms1 <= ms2 must never shift the
# converted delay EARLIER -- the "causality cannot silently reorder" guard.
# (The machine's per-tick step is a +0/+1 pick, which is the shape BendTT
# can induct on; the divmod-closed form cannot reduce on symbolic ms.)
# --------------------------------------------------------------------------

# the per-tick form: converting 1 more ms-tick never DECREASES the steps
law mdelay_micro:
  for +ms: Nat
  for +dt: Nat
  {Nat.is_le(M.ms_to_steps(ms, dt), M.ms_to_steps(1n+ms, dt)) == True{} : Bool}

# THE quantified monotonicity law, decider-witness form
law mdelay_mono:
  for +ms1: Nat
  for +ms2: Nat
  for +dt: Nat
  for h: R.le_ok(ms1, ms2)
  {Nat.is_le(M.ms_to_steps(ms1, dt), M.ms_to_steps(ms2, dt)) == True{} : Bool}

# strict increase WHERE THE RANGE ALLOWS: an ms delay whose NEXT tick is a
# rounding boundary (at_next on the machine state) converts to a step count
# strictly below its successor's -- the boundary ADDS its step (the
# half-step plateau cannot silently absorb a boundary the rule says fires).
law mdelay_cross:
  for +ms1: Nat
  for +dt: Nat
  for +hjs: {M.at_next(M.ms_at(ms1, dt)) == True{} : Bool}
  {Nat.is_ne(M.ms_to_steps(ms1, dt),
             M.ms_to_steps(Nat.add(ms1, 1n), dt)) == True{} : Bool}

# --------------------------------------------------------------------------
# the validator's instance pins (the mc_ok_good / mc_ok_bad_cvar pattern):
# --------------------------------------------------------------------------

# the demo's network with per-lane dt 0.1 ms and a 0.2 ms coupling delay is
# ACCEPTED: one dt per lane, one ms delay per projection, both dts >= 1,
# the nonzero delay converts to 2 >= 1 steps, base R.ok green.
law md_ok_good:
  {M.md_ok(GOOD_DTS(), GOOD_MSDS(), GOOD_C()) == True{} : Bool}

# the guard's red pin: the SAME network with the 0.04 ms sub-step delay
# (rounds to 0 steps) is REJECTED -- a nonzero delay collapsing onto the
# zero-step read would silently merge two causalities onto one line.
law md_ok_bad_substep:
  {M.md_ok(GOOD_DTS(), SUBSTEP_MSDS(), GOOD_C()) == False{} : Bool}
