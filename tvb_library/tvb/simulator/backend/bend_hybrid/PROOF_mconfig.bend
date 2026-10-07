# PROOF_mconfig.bend -- the proofs for LAWS_mconfig.bend.  The gate:
#
#   bend PROOF_mconfig.bend            must print ALL PROOFS CHECK
#   bend PROOF_mconfig.bend --verdict  re-checked by the Lean-proved kernel
#
# House style (PROOF_router.bend / PROOF_sweep.bend): quantified laws go
# through go-lemmas that match the shrinking argument plus the witnesses;
# witness types (R.lt_ok) refine by passing the peeled witness straight
# through (lt_ok(1n+q, 1n+L) and lt_ok(q, L) share the normal form
# le_ok(1n+q, L)); {==} closes what normalises; the and-elimination
# helpers are PROOF_router's plain defs (PR.and_elim_l_go / and_elim_r_go
# -- plain defs re-export across module imports where filled laws do
# not).  The capstone's index transport is the sw_le_b/b_le Bool
# roundtrip (copied from PROOF_sweep.bend, which copied it for the same
# reason: the le_ok_iff law fill does not re-export).
import Base
import ./LAWS_mconfig.bend as Laws
import ./mconfig.bend as M
import ./router.bend as R
import ./sweep.bend as S
import ./PROOF_router.bend as PR

# False is not True: the motive sends True to Empty, so transporting along a
# proof of {False == True} lands in Empty and anything follows.
def Bool.mot(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def Bool.fne(-A: Type, e: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, (%e : Bool.mot(_)
  Unit{}))

# the Type->Bool direction for an lt_ok witness is NOT needed here: the
# capstone's index witness is stated in Bool form directly (see
# LAWS_mconfig.mc_contract), so both consumers rebuild their own Type
# witness from it with PR.b_le.

# --------------------------------------------------------------------------
# the instance pins: pure computation, definitional
# --------------------------------------------------------------------------

def Laws.mc_ok_good():
  {==}

def Laws.mc_ok_bad_cvar():
  {==}

# --------------------------------------------------------------------------
# the inversion family: mc_ok == True decomposes into its four flat
# conjuncts, one and_elim walk each (PR.and_elim_l_go / and_elim_r_go)
# --------------------------------------------------------------------------

def Laws.mc_ok_shape(shapes, mps, c, h):
  PR.and_elim_l_go(Nat.is_eq(R.nats_len(shapes), R.nats_len(R.cfg_lanes(c))),
                   Bool.and(M.mprojs_src_ok(shapes, mps),
                   Bool.and(M.mprojs_tgt_ok(shapes, mps),
                            R.ok(c))),
                   h)

def Laws.mc_ok_src_cvar(shapes, mps, c, h):
  +h2 = h
  PR.and_elim_l_go(M.mprojs_src_ok(shapes, mps),
                   Bool.and(M.mprojs_tgt_ok(shapes, mps), R.ok(c)),
                   PR.and_elim_r_go(Nat.is_eq(R.nats_len(shapes), R.nats_len(R.cfg_lanes(c))),
                                    Bool.and(M.mprojs_src_ok(shapes, mps),
                                    Bool.and(M.mprojs_tgt_ok(shapes, mps),
                                             R.ok(c))),
                                    h2))

def Laws.mc_ok_tgt_cvar(shapes, mps, c, h):
  +h2 = h
  PR.and_elim_l_go(M.mprojs_tgt_ok(shapes, mps), R.ok(c),
                   PR.and_elim_r_go(M.mprojs_src_ok(shapes, mps),
                                    Bool.and(M.mprojs_tgt_ok(shapes, mps), R.ok(c)),
                                    PR.and_elim_r_go(Nat.is_eq(R.nats_len(shapes), R.nats_len(R.cfg_lanes(c))),
                                                     Bool.and(M.mprojs_src_ok(shapes, mps),
                                                     Bool.and(M.mprojs_tgt_ok(shapes, mps),
                                                              R.ok(c))),
                                                     h2)))

def Laws.mc_ok_base(shapes, mps, c, h):
  PR.and_elim_r_go(M.mprojs_tgt_ok(shapes, mps), R.ok(c),
                   PR.and_elim_r_go(M.mprojs_src_ok(shapes, mps),
                                    Bool.and(M.mprojs_tgt_ok(shapes, mps), R.ok(c)),
                                    PR.and_elim_r_go(Nat.is_eq(R.nats_len(shapes), R.nats_len(R.cfg_lanes(c))),
                                                     Bool.and(M.mprojs_src_ok(shapes, mps),
                                                     Bool.and(M.mprojs_tgt_ok(shapes, mps),
                                                              R.ok(c))),
                                                     h)))

# --------------------------------------------------------------------------
# the per-index forms: induction on the view, peeling the index.  The
# Nil case is absurd (i < 0, through PR.lt_ok_nil_absurd); the head case
# is the fold's head conjunct; the succ case recurses into the tail with
# the tail conjunct.  The peeled witness passes straight through:
# lt_ok(1n+q, 1n+|tail|) and lt_ok(q, |tail|) share the normal form.
# --------------------------------------------------------------------------

def mc_src_nth_go(+shapes: List<&2, Nat>, +mps: List<&2, M.MProj>, +i: Nat,
                  h: R.lt_ok(i, M.mprojs_len(mps)),
                  hok: {M.mprojs_src_ok(shapes, mps) == True{} : Bool})
    -> {M.mproj_src_ok(shapes, M.nth_mproj(mps, i)) == True{} : Bool}:
  match mps i h:
    case Nil{} _ h:
      Empty.absurd({M.mproj_src_ok(shapes, M.nth_mproj(Nil{}, i)) == True{} : Bool},
                   PR.lt_ok_nil_absurd(i, h))
    case p <> t 0n _:
      PR.and_elim_l_go(M.mproj_src_ok(shapes, p), M.mprojs_src_ok(shapes, t), hok)
    case p <> t 1n+q hlt:
      mc_src_nth_go(shapes, t, q, hlt,
                    PR.and_elim_r_go(M.mproj_src_ok(shapes, p),
                                     M.mprojs_src_ok(shapes, t), hok))

def Laws.mc_src_nth(shapes, mps, i, h, hok):
  mc_src_nth_go(shapes, mps, i, h, hok)

def mc_tgt_nth_go(+shapes: List<&2, Nat>, +mps: List<&2, M.MProj>, +i: Nat,
                  h: R.lt_ok(i, M.mprojs_len(mps)),
                  hok: {M.mprojs_tgt_ok(shapes, mps) == True{} : Bool})
    -> {M.mproj_tgt_ok(shapes, M.nth_mproj(mps, i)) == True{} : Bool}:
  match mps i h:
    case Nil{} _ h:
      Empty.absurd({M.mproj_tgt_ok(shapes, M.nth_mproj(Nil{}, i)) == True{} : Bool},
                   PR.lt_ok_nil_absurd(i, h))
    case p <> t 0n _:
      PR.and_elim_l_go(M.mproj_tgt_ok(shapes, p), M.mprojs_tgt_ok(shapes, t), hok)
    case p <> t 1n+q hlt:
      mc_tgt_nth_go(shapes, t, q, hlt,
                    PR.and_elim_r_go(M.mproj_tgt_ok(shapes, p),
                                     M.mprojs_tgt_ok(shapes, t), hok))

def Laws.mc_tgt_nth(shapes, mps, i, h, hok):
  mc_tgt_nth_go(shapes, mps, i, h, hok)

# --------------------------------------------------------------------------
# the pairing laws: induction on the projections, peeling the index.
# mview recurses on the projections ONLY (the cvar lists ride through
# nats_nth/nats_tail), so the head's src/tgt fields normalize without
# case-splitting the cvar lists and the recursion is direct.
# --------------------------------------------------------------------------

def mview_len_go(+ps: List<&2, R.Proj>, +svs: List<&2, Nat>, +tvs: List<&2, Nat>)
    -> {M.mprojs_len(M.mview(ps, svs, tvs)) == R.projs_len(ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case p <> t:
      Equal.cong(Nat, Nat, n => Nat.add(1n, n),
                 M.mprojs_len(M.mview(t, M.nats_tail(svs), M.nats_tail(tvs))),
                 R.projs_len(t),
                 mview_len_go(t, M.nats_tail(svs), M.nats_tail(tvs)))

def Laws.mview_len(ps, svs, tvs):
  mview_len_go(ps, svs, tvs)

def mview_src_nth_go(+ps: List<&2, R.Proj>, +svs: List<&2, Nat>, +tvs: List<&2, Nat>,
                     +i: Nat, h: R.lt_ok(i, R.projs_len(ps)))
    -> {M.mproj_src(M.nth_mproj(M.mview(ps, svs, tvs), i))
          == R.proj_src(R.nth_proj(ps, i)) : Nat}:
  match ps i h:
    case Nil{} _ h:
      Empty.absurd({M.mproj_src(M.nth_mproj(M.mview(Nil{}, svs, tvs), i))
                      == R.proj_src(R.nth_proj(Nil{}, i)) : Nat},
                   PR.lt_ok_nil_absurd(i, h))
    case p <> t 0n _:
      {==}
    case p <> t 1n+q hlt:
      mview_src_nth_go(t, M.nats_tail(svs), M.nats_tail(tvs), q, hlt)

def Laws.mview_src_nth(ps, svs, tvs, i, h):
  mview_src_nth_go(ps, svs, tvs, i, h)

def mview_tgt_nth_go(+ps: List<&2, R.Proj>, +svs: List<&2, Nat>, +tvs: List<&2, Nat>,
                     +i: Nat, h: R.lt_ok(i, R.projs_len(ps)))
    -> {M.mproj_tgt(M.nth_mproj(M.mview(ps, svs, tvs), i))
          == R.proj_tgt(R.nth_proj(ps, i)) : Nat}:
  match ps i h:
    case Nil{} _ h:
      Empty.absurd({M.mproj_tgt(M.nth_mproj(M.mview(Nil{}, svs, tvs), i))
                      == R.proj_tgt(R.nth_proj(Nil{}, i)) : Nat},
                   PR.lt_ok_nil_absurd(i, h))
    case p <> t 0n _:
      {==}
    case p <> t 1n+q hlt:
      mview_tgt_nth_go(t, M.nats_tail(svs), M.nats_tail(tvs), q, hlt)

def Laws.mview_tgt_nth(ps, svs, tvs, i, h):
  mview_tgt_nth_go(ps, svs, tvs, i, h)

# --------------------------------------------------------------------------
# THE CAPSTONE: mc_contract.  Three components, one pair-of-pairs
# equality.  The cvar halves come from the per-index laws -- but their
# witness is on the VIEW's length while hi is on the projections', so
# the index is transported ONCE through mview_len by the Bool roundtrip
# (witness -> Bool claim, cong along the length equality, Bool ->
# witness).  The routing half is the bridge PR.routing_contract_at (the
# routing_contract law at the shared config, ties {==} since the law
# instantiates ls/ps definitionally), exactly as sweep_contract's third
# conjunct is discharged.  The three component equalities assemble into
# the triple by cong on each component + Equal.trans, the sweep_contract
# assembly.
# --------------------------------------------------------------------------

def Laws.mc_contract(shapes, svs, tvs, c, t, i, h, hib):
  +mv = M.mview(R.cfg_projs(c), svs, tvs)
  # the four mc_ok conjuncts (h rides in three copies, the +h2 idiom)
  +h2 = h
  +h3 = h2
  hbase = Laws.mc_ok_base(shapes, mv, c, h)
  hsrcf = Laws.mc_ok_src_cvar(shapes, mv, c, h2)
  htgtf = Laws.mc_ok_tgt_cvar(shapes, mv, c, h3)
  # the index transport: the Bool witness -> a view-length Bool claim,
  # through mview_len (the length equality) by cong
  +e_len = Equal.sym(Nat, M.mprojs_len(mv), R.projs_len(R.cfg_projs(c)),
                    Laws.mview_len(R.cfg_projs(c), svs, tvs))
  +hiC = Equal.cong(Nat, Bool, x => Nat.is_le(Nat.add(i, 1n), x),
                   R.projs_len(R.cfg_projs(c)), M.mprojs_len(mv), e_len)
  +hiC2 = Equal.sym(Bool,
                   Nat.is_le(Nat.add(i, 1n), R.projs_len(R.cfg_projs(c))),
                   Nat.is_le(Nat.add(i, 1n), M.mprojs_len(mv)), hiC)
  +hiView = Equal.trans(Bool,
                       Nat.is_le(Nat.add(i, 1n), M.mprojs_len(mv)),
                       Nat.is_le(Nat.add(i, 1n), R.projs_len(R.cfg_projs(c))),
                       True{}, hiC2, hib)
  # the three components (each rebuilds its own Type witness from the
  # Bool form -- witnesses are not +able, the Bool proofs are)
  hiV1 = PR.b_le(Nat.add(i, 1n), M.mprojs_len(mv), hiView)
  hiV2 = PR.b_le(Nat.add(i, 1n), M.mprojs_len(mv), hiView)
  hb = PR.b_le(Nat.add(i, 1n), R.projs_len(R.cfg_projs(c)), hib)
  hsrc = Laws.mc_src_nth(shapes, mv, i, hiV1, hsrcf)
  htgt = Laws.mc_tgt_nth(shapes, mv, i, hiV2, htgtf)
  hroute = PR.routing_contract_at(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c),
                                  t, i, hbase, {==}, {==}, hb)
  # the assembly: (a, b, r) == (True, True, True), cong per component
  Equal.trans(Bool & (Bool & Bool),
    (M.mproj_src_ok(shapes, M.nth_mproj(mv, i)),
     M.mproj_tgt_ok(shapes, M.nth_mproj(mv, i)),
     S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), t, i)),
    (True{}, M.mproj_tgt_ok(shapes, M.nth_mproj(mv, i)),
     S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), t, i)),
    (True{}, True{}, True{}),
    Equal.cong(Bool, Bool & (Bool & Bool),
               x => (x,
                     M.mproj_tgt_ok(shapes, M.nth_mproj(mv, i)),
                     S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), t, i)),
               M.mproj_src_ok(shapes, M.nth_mproj(mv, i)), True{}, hsrc),
    Equal.trans(Bool & (Bool & Bool),
      (True{}, M.mproj_tgt_ok(shapes, M.nth_mproj(mv, i)),
       S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), t, i)),
      (True{}, True{},
       S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), t, i)),
      (True{}, True{}, True{}),
      Equal.cong(Bool, Bool & (Bool & Bool),
                 y => (True{}, y,
                       S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), t, i)),
                 M.mproj_tgt_ok(shapes, M.nth_mproj(mv, i)), True{}, htgt),
      Equal.cong(Bool, Bool & (Bool & Bool),
                 z => (True{}, True{}, z),
                 S.routing_bundle(c, R.init_lanes(R.cfg_lanes(c)), R.cfg_projs(c), t, i),
                 True{}, hroute)))

# --------------------------------------------------------------------------
# P3a -- the per-lane SCHEME layer: proofs
# --------------------------------------------------------------------------
# the instance pins: pure computation on the literal tables, assignment,
# and config -- every conjunct computes on concrete input.
def Laws.scheme_ok_good():
  {==}

def Laws.scheme_ok_bad():
  {==}

# the inversion family: scheme_ok == True decomposes into its three flat
# conjuncts (is_eq-len /\ (bounds-fold /\ mc_ok)), one and_elim walk each
# (the mc_ok_shape family's walk, one level shallower).
def Laws.scheme_ok_len(table, schemes, shapes, mps, c, h):
  PR.and_elim_l_go(Nat.is_eq(R.nats_len(schemes), R.nats_len(R.cfg_lanes(c))),
                   Bool.and(M.schemes_ok(schemes, R.nats_len(table)),
                            M.mc_ok(shapes, mps, c)),
                   h)

def Laws.scheme_ok_bounds(table, schemes, shapes, mps, c, h):
  PR.and_elim_l_go(M.schemes_ok(schemes, R.nats_len(table)),
                   M.mc_ok(shapes, mps, c),
                   PR.and_elim_r_go(Nat.is_eq(R.nats_len(schemes),
                                              R.nats_len(R.cfg_lanes(c))),
                                    Bool.and(M.schemes_ok(schemes,
                                                          R.nats_len(table)),
                                             M.mc_ok(shapes, mps, c)),
                                    h))

def Laws.scheme_ok_base(table, schemes, shapes, mps, c, h):
  PR.and_elim_r_go(M.schemes_ok(schemes, R.nats_len(table)),
                   M.mc_ok(shapes, mps, c),
                   PR.and_elim_r_go(Nat.is_eq(R.nats_len(schemes),
                                              R.nats_len(R.cfg_lanes(c))),
                                    Bool.and(M.schemes_ok(schemes,
                                                          R.nats_len(table)),
                                             M.mc_ok(shapes, mps, c)),
                                    h))

# scheme_bounded: induction on the assignment list, peeling the lane
# index.  The Nil case is absurd (i < 0, through PR.lt_ok_nil_absurd);
# the head case is the fold's head conjunct (nats_nth(s0 <> t, 0n)
# reduces to s0); the succ case recurses into the tail with the tail
# conjunct, the peeled witness passing straight through.
def scheme_bounded_go(schemes: List<&2, Nat>, +ntab: Nat, i: Nat,
                      h: R.lt_ok(i, R.nats_len(schemes)),
                      hok: {M.schemes_ok(schemes, ntab) == True{} : Bool})
    -> {Nat.is_lt(R.nats_nth(schemes, i), ntab) == True{} : Bool}:
  match schemes i h:
    case Nil{} _ hlt:
      Empty.absurd({Nat.is_lt(R.nats_nth(Nil{}, i), ntab) == True{} : Bool},
                   PR.lt_ok_nil_absurd(i, hlt))
    case s0 <> +t 0n _:
      PR.and_elim_l_go(Nat.is_lt(s0, ntab), M.schemes_ok(t, ntab), hok)
    case s0 <> +t 1n+q hlt:
      scheme_bounded_go(t, ntab, q, hlt,
                        PR.and_elim_r_go(Nat.is_lt(s0, ntab),
                                         M.schemes_ok(t, ntab), hok))

def Laws.scheme_bounded(schemes, ntab, i, h, hok):
  scheme_bounded_go(schemes, ntab, i, h, hok)

# scheme_nth: the resolved scheme reads the table THROUGH the lane's id
# -- a congruence under nats_nth(table, ·) along the id hypothesis.
def Laws.scheme_nth(table, schemes, i, hid):
  Equal.cong(Nat, Nat, x => R.nats_nth(table, x),
             M.lane_scheme(schemes, i), i, hid)

# the instance pins: pure computation on the literal identity assignment
# -- lane 0's read lands on table entry 0, lane 1's on entry 1.
def Laws.scheme_nth_inst_0():
  {==}

def Laws.scheme_nth_inst_1():
  {==}

# --------------------------------------------------------------------------
# P4 -- the cvar NAME-RESOLUTION proofs.
# --------------------------------------------------------------------------

# Bool.not inversion: from {Bool.not(b) == True} conclude {b == False}.
# The True case is absurd (Bool.not(True{}) == True{} normalises to
# {False == True}, Bool.fne's contradiction); the False case is {==}.
def not_true(b: Bool, hb: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Bool.fne({True{} == False{} : Bool}, hb)
    case False{}:
      {==}

# the instance pins: pure computation on the literal name lists --
# String.eq computes on literals, so the whole lookup folds out.
def Laws.cvar_resolve_instance_jr():
  {==}

def Laws.cvar_resolve_cross():
  {==}

def Laws.cvar_ok_good():
  {==}

# cvar_resolve_unknown: induction on the name list.  The Nil case is the
# junk index on the empty list (both sides 0n); the cons case peels the
# head's decision -- the absence fold gives String.eq(h, name) == False,
# so the lookup takes the Bool.pick false arm (1n + the tail's lookup)
# and the induction hypothesis re-composes the length.  A cong THROUGH
# the Bool.pick decision moves the goal onto the false arm -- the pick
# scrutinee is a parameter of the pick, not a computed value inside a
# def, so Equal.cong reaches it (the slot_of idiom's proof shape).
def find_unknown_go(names: List<&2, String>, +name: String,
                   +habs: {M.not_in(names, name) == True{} : Bool})
    -> {M.find_name(names, name) == M.snames_len(names) : Nat}:
  match names:
    case Nil{}:
      {==}
    case +h <> +t:
      +habs2 = habs
      +nm2 = name
      hb = PR.and_elim_l_go(Bool.not(String.eq(h, nm2)), M.not_in(t, nm2), habs)
      he = not_true(String.eq(h, nm2), hb)
      ih = find_unknown_go(t, nm2, PR.and_elim_r_go(Bool.not(String.eq(h, nm2)),
                                                    M.not_in(t, nm2), habs2))
      Equal.trans(Nat,
        M.find_name(h <> t, nm2),
        Bool.pick(Nat, False{}, 0n, Nat.add(1n, M.find_name(t, nm2))),
        M.snames_len(h <> t),
        Equal.cong(Bool, Nat,
                   x => Bool.pick(Nat, x, 0n, Nat.add(1n, M.find_name(t, nm2))),
                   String.eq(h, nm2), False{}, he),
        Equal.cong(Nat, Nat, n => Nat.add(1n, n),
                   M.find_name(t, nm2), M.snames_len(t), ih))

def Laws.cvar_resolve_unknown(names, name, habs):
  find_unknown_go(names, name, habs)

# cvar_resolve_found: induction on the list/index pair, peeling both.
# The Nil case is absurd (the index is bounded by the list's length,
# PR.lt_ok_nil_absurd); the 0n case rewrites the head's decision onto
# the True arm through the presence hypothesis (Bool form, so the cong
# is direct); the succ case splits the freshness fold into the head's
# absence (String.eq(h, name) == False -- the false arm) and the tail's
# freshness (the induction hypothesis), and re-composes with 1n + .
def find_found_go(names: List<&2, String>, +name: String, k: Nat,
                  +hpos: {String.eq(S.str_nth(names, k), name) == True{} : Bool},
                  +hfresh: {M.not_before(names, name, k) == True{} : Bool},
                  h: R.lt_ok(k, M.snames_len(names)))
    -> {M.find_name(names, name) == k : Nat}:
  match names k h:
    case Nil{} _ h:
      Empty.absurd({M.find_name(Nil{}, name) == k : Nat},
                   PR.lt_ok_nil_absurd(k, h))
    case +h0 <> +t 0n _:
      Equal.trans(Nat,
        M.find_name(h0 <> t, name),
        Bool.pick(Nat, True{}, 0n, Nat.add(1n, M.find_name(t, name))),
        0n,
        Equal.cong(Bool, Nat,
                   x => Bool.pick(Nat, x, 0n, Nat.add(1n, M.find_name(t, name))),
                   String.eq(h0, name), True{}, hpos),
        {==})
    case +h0 <> +t 1n+(+q) hlt:
      +hpos2 = hpos
      +q2 = q
      +nm2 = name
      hb = PR.and_elim_l_go(Bool.not(String.eq(h0, name)),
                            M.not_before(t, name, q), hfresh)
      he = not_true(String.eq(h0, name), hb)
      ih = find_found_go(t, name, q2, hpos2,
                         PR.and_elim_r_go(Bool.not(String.eq(h0, name)),
                                          M.not_before(t, name, q), hfresh),
                         hlt)
      Equal.trans(Nat,
        M.find_name(h0 <> t, name),
        Nat.add(1n, M.find_name(t, name)),
        Nat.add(1n, q2),
        Equal.cong(Bool, Nat,
                   x => Bool.pick(Nat, x, 0n, Nat.add(1n, M.find_name(t, nm2))),
                   String.eq(h0, name), False{}, he),
        Equal.cong(Nat, Nat, n => Nat.add(1n, n),
                   M.find_name(t, name), q2, ih))

def Laws.cvar_resolve_found(names, name, k, hpos, hfresh, h):
  find_found_go(names, name, k, hpos, hfresh, h)

# mnview_len: induction on the named projections (the mview_len_go
# pattern -- mnview recurses on the projections only, the model lists
# ride along unpeeled).
def mnview_len_go(+nps: List<&2, M.NProj>, +ms: List<&2, List<&2, String>>)
    -> {M.mprojs_len(M.mnview(nps, ms)) == M.nprojs_len(nps) : Nat}:
  match nps:
    case Nil{}:
      {==}
    case np <> t:
      Equal.cong(Nat, Nat, n => Nat.add(1n, n),
                 M.mprojs_len(M.mnview(t, ms)), M.nprojs_len(t),
                 mnview_len_go(t, ms))

def Laws.mnview_len(nps, ms):
  mnview_len_go(nps, ms)

# the pairing halves: induction on the named projections, peeling the
# index.  The head case is definitional (mview row 0's fields ARE the
# head NProj's resolution); the succ case recurses into the tail -- the
# peeled witness passes straight through (lt_ok(1n+q, 1n+L) and
# lt_ok(q, L) share the normal form).
def svar_pair_go(nps: List<&2, M.NProj>, +ms: List<&2, List<&2, String>>,
                 i: Nat, h: R.lt_ok(i, M.nprojs_len(nps)))
    -> {M.mproj_svar(M.nth_mproj(M.mnview(nps, ms), i))
          == M.find_name(M.nth_snames(ms, M.mproj_src(M.nth_mproj(M.mnview(nps, ms), i))),
                         M.nproj_sname(M.nth_nproj(nps, i))) : Nat}:
  match nps i h:
    case Nil{} _ h:
      Empty.absurd({M.mproj_svar(M.nth_mproj(M.mnview(Nil{}, ms), i))
                      == M.find_name(M.nth_snames(ms, M.mproj_src(M.nth_mproj(M.mnview(Nil{}, ms), i))),
                                     M.nproj_sname(M.nth_nproj(Nil{}, i))) : Nat},
                   PR.lt_ok_nil_absurd(i, h))
    case np <> t 0n _:
      {==}
    case np <> t 1n+q hlt:
      svar_pair_go(t, ms, q, hlt)

def tcvar_pair_go(nps: List<&2, M.NProj>, +ms: List<&2, List<&2, String>>,
                  i: Nat, h: R.lt_ok(i, M.nprojs_len(nps)))
    -> {M.mproj_tcvar(M.nth_mproj(M.mnview(nps, ms), i))
          == M.find_name(M.nth_snames(ms, M.mproj_tgt(M.nth_mproj(M.mnview(nps, ms), i))),
                         M.nproj_tname(M.nth_nproj(nps, i))) : Nat}:
  match nps i h:
    case Nil{} _ h:
      Empty.absurd({M.mproj_tcvar(M.nth_mproj(M.mnview(Nil{}, ms), i))
                      == M.find_name(M.nth_snames(ms, M.mproj_tgt(M.nth_mproj(M.mnview(Nil{}, ms), i))),
                                     M.nproj_tname(M.nth_nproj(Nil{}, i))) : Nat},
                   PR.lt_ok_nil_absurd(i, h))
    case np <> t 0n _:
      {==}
    case np <> t 1n+q hlt:
      tcvar_pair_go(t, ms, q, hlt)

# cvar_resolve_proj: the two halves assemble into the pair equality by
# cong per component + Equal.trans (the mc_contract assembly, two
# components).  Each half rebuilds its own Type witness from the Bool
# form -- witnesses are not +able, the Bool proofs are.
def Laws.cvar_resolve_proj(nps, ms, i, hib):
  +hib2 = hib
  +v = M.nth_mproj(M.mnview(nps, ms), i)
  +np = M.nth_nproj(nps, i)
  hs1 = PR.b_le(Nat.add(i, 1n), M.nprojs_len(nps), hib)
  hs2 = PR.b_le(Nat.add(i, 1n), M.nprojs_len(nps), hib2)
  hsvar = svar_pair_go(nps, ms, i, hs1)
  htcvar = tcvar_pair_go(nps, ms, i, hs2)
  Equal.trans(Nat & Nat,
    (M.mproj_svar(v), M.mproj_tcvar(v)),
    (M.find_name(M.nth_snames(ms, M.mproj_src(v)), M.nproj_sname(np)),
     M.mproj_tcvar(v)),
    (M.find_name(M.nth_snames(ms, M.mproj_src(v)), M.nproj_sname(np)),
     M.find_name(M.nth_snames(ms, M.mproj_tgt(v)), M.nproj_tname(np))),
    Equal.cong(Nat, Nat & Nat,
               x => (x, M.mproj_tcvar(v)),
               M.mproj_svar(v),
               M.find_name(M.nth_snames(ms, M.mproj_src(v)), M.nproj_sname(np)),
               hsvar),
    Equal.cong(Nat, Nat & Nat,
               y => (M.find_name(M.nth_snames(ms, M.mproj_src(v)), M.nproj_sname(np)), y),
               M.mproj_tcvar(v),
               M.find_name(M.nth_snames(ms, M.mproj_tgt(v)), M.nproj_tname(np)),
               htcvar))

# cvar_resolve_bounded: the pairing half (svar_pair_go) rewrites the
# resolved index onto the view row's svar, and the mc_ok source bound at
# that row (mc_src_nth through the and-eliminated mc_ok conjunct)
# finishes -- the composition the law claims.  The index is transported
# once through mnview_len by the Bool roundtrip (the mc_contract
# pattern) because the pairing consumes the nps-length witness while
# mc_src_nth consumes the view-length one.
def Laws.cvar_resolve_bounded(nps, ms, shapes, c, i, hib, hok):
  +v = M.nth_mproj(M.mnview(nps, ms), i)
  +np = M.nth_nproj(nps, i)
  +e_len = Laws.mnview_len(nps, ms)
  hn = PR.b_le(Nat.add(i, 1n), M.nprojs_len(nps), hib)
  hiC = Equal.cong(Nat, Bool, x => Nat.is_le(Nat.add(i, 1n), x),
                   M.nprojs_len(nps), M.mprojs_len(M.mnview(nps, ms)),
                   Equal.sym(Nat, M.mprojs_len(M.mnview(nps, ms)),
                             M.nprojs_len(nps), e_len))
  hiC2 = Equal.sym(Bool,
                   Nat.is_le(Nat.add(i, 1n), M.nprojs_len(nps)),
                   Nat.is_le(Nat.add(i, 1n), M.mprojs_len(M.mnview(nps, ms))),
                   hiC)
  hiV = Equal.trans(Bool,
                   Nat.is_le(Nat.add(i, 1n), M.mprojs_len(M.mnview(nps, ms))),
                   Nat.is_le(Nat.add(i, 1n), M.nprojs_len(nps)),
                   True{}, hiC2, hib)
  hb = PR.b_le(Nat.add(i, 1n), M.mprojs_len(M.mnview(nps, ms)), hiV)
  hsrcf = Laws.mc_ok_src_cvar(shapes, M.mnview(nps, ms), c, hok)
  hbound = Laws.mc_src_nth(shapes, M.mnview(nps, ms), i, hb, hsrcf)
  hs = svar_pair_go(nps, ms, i, hn)
  hsA = Equal.sym(Nat, M.mproj_svar(v),
                  M.find_name(M.nth_snames(ms, M.mproj_src(v)), M.nproj_sname(np)), hs)
  Equal.trans(Bool,
    Nat.is_lt(M.find_name(M.nth_snames(ms, M.mproj_src(v)), M.nproj_sname(np)),
              R.nats_nth(shapes, M.mproj_src(v))),
    Nat.is_lt(M.mproj_svar(v), R.nats_nth(shapes, M.mproj_src(v))),
    True{},
    Equal.cong(Nat, Bool, x => Nat.is_lt(x, R.nats_nth(shapes, M.mproj_src(v))),
               M.find_name(M.nth_snames(ms, M.mproj_src(v)), M.nproj_sname(np)),
               M.mproj_svar(v), hsA),
    hbound)
