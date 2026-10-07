# mconfig.bend -- the CONFIG-COMPLEXITY layer: heterogeneous subnets.
#
# The router's Config (router.bend) carries per-lane PERIODS only; its
# Proj carries the target coupling slot (tc) and abstracts the source
# cvar away.  The hybrid demos (simulate_hybrid_getting_started.py) are
# one level richer: each Subnetwork carries a MODEL -- JansenRit (6
# state variables, cvar list of 2) paired with ReducedSetFitzHughNagumo
# (its own state_variables, cvar list of 1) -- and an InterProjection
# maps NAMED cvars across models (source_cvar='y1' on the source model,
# target_cvar='xi' on the target model): the coupling slot is
# MODEL-RELATIVE, resolved against each model's own state_variables.
#
# This layer models exactly that, WITHOUT touching router.bend:
#
# REPRESENTATION CHOICES (both documented, both minimal):
#
#   * MODEL SHAPE = a plain `List<&2, Nat>` of cvar counts, one entry
#     per subnet/lane (cortex: 2, thalamus: 1 in the demo).  A
#     ModelShape{n_cvars} record would wrap one Nat; the validator and
#     every law only ever read the count, so the bare list reuses the
#     router's nats_len/nats_nth conventions (default 0 past the end)
#     and adds no vocabulary.
#
#   * PROJECTION VIEW = a PARALLEL `List<&2, MProj>` keyed by
#     projection index, MProj{src, tgt, svar, tcvar}: src/tgt are
#     copied from the plain projection (so the PAIRING laws can tie the
#     view to the config), svar/tcvar are the MODEL-RELATIVE cvar
#     indices -- the demo's named cvars ('y1', 'xi') resolved to
#     indices against the RESPECTIVE models.  The view is BUILT by
#     `mview` from the plain projections plus per-projection cvar-index
#     lists (default 0n past their end, the nats_nth convention), so
#     the pairing laws have a constructor to be proven about.
#
# The validator `mc_ok` accepts (shapes, mps, c) iff:
#   (a) the shape list has exactly one entry per lane;
#   (b) every projection's source cvar < the source lane's model cvar
#       count;
#   (c) every projection's target cvar < the target lane's model cvar
#       count;
#   (d) the plain config passes R.ok.
# The four conjuncts are spelled FLAT (and-of-and), the section-6
# and-elimination shape: each inversion law is one and_elim walk.
# Note (b)/(c) subsume the view's src/tgt lane bounds: past the shape
# list's end nats_nth answers 0n, and is_lt(svar, 0n) is False for every
# svar -- an out-of-range lane index is rejected, not defaulted.
# (What mc_ok does NOT pin is |mps| == |projs|; the view constructor
# mview guarantees it, and LAWS_mconfig.mview_len pins it.)

import ./router.bend as R

# --------------------------------------------------------------------------
# the heterogeneous projection view
# --------------------------------------------------------------------------

type MProj is Data:
  MProj{src: Nat, tgt: Nat, svar: Nat, tcvar: Nat}

def mproj_src(+p: MProj) -> Nat:
  match p:
    case MProj{src, tgt, svar, tcvar}:
      src

def mproj_tgt(+p: MProj) -> Nat:
  match p:
    case MProj{src, tgt, svar, tcvar}:
      tgt

def mproj_svar(+p: MProj) -> Nat:
  match p:
    case MProj{src, tgt, svar, tcvar}:
      svar

def mproj_tcvar(+p: MProj) -> Nat:
  match p:
    case MProj{src, tgt, svar, tcvar}:
      tcvar

def mprojs_len(mps: List<&2, MProj>) -> Nat:
  match mps:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(1n, mprojs_len(t))

# nth element of the view, defaulting past the end (the nth_proj
# convention; the per-index laws carry lt_ok bounds witnesses so the
# default branch is never trusted)
def nth_mproj(mps: List<&2, MProj>, i: Nat) -> MProj:
  match mps i:
    case Nil{} _:
      MProj{0n, 0n, 0n, 0n}
    case h <> t 0n:
      h
    case h <> t 1n+p:
      nth_mproj(t, p)

def nats_tail(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

# the view constructor: one MProj per plain projection, src/tgt copied,
# svar/tcvar taken positionally from the cvar-index lists (0n past the
# end, the nats_nth convention).  Recursion is on the PROJECTIONS only:
# the cvar lists ride along through nats_nth/nats_tail, so the head's
# src/tgt fields normalize without case-splitting the cvar lists -- the
# shape the pairing laws are proven in.
def mview(ps: List<&2, R.Proj>, +svs: List<&2, Nat>, +tvs: List<&2, Nat>)
    -> List<&2, MProj>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      MProj{R.proj_src(p), R.proj_tgt(p), R.nats_nth(svs, 0n), R.nats_nth(tvs, 0n)}
        <> mview(t, nats_tail(svs), nats_tail(tvs))

# --------------------------------------------------------------------------
# the validator: the four conjuncts, flat
# --------------------------------------------------------------------------

# (b) the source cvar is inside the SOURCE lane's model cvar count
def mproj_src_ok(+shapes: List<&2, Nat>, +p: MProj) -> Bool:
  Nat.is_lt(mproj_svar(p), R.nats_nth(shapes, mproj_src(p)))

# (c) the target cvar is inside the TARGET lane's model cvar count
def mproj_tgt_ok(+shapes: List<&2, Nat>, +p: MProj) -> Bool:
  Nat.is_lt(mproj_tcvar(p), R.nats_nth(shapes, mproj_tgt(p)))

def mprojs_src_ok(+shapes: List<&2, Nat>, mps: List<&2, MProj>) -> Bool:
  match mps:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(mproj_src_ok(shapes, h), mprojs_src_ok(shapes, t))

def mprojs_tgt_ok(+shapes: List<&2, Nat>, mps: List<&2, MProj>) -> Bool:
  match mps:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(mproj_tgt_ok(shapes, h), mprojs_tgt_ok(shapes, t))

# THE VALIDATOR.  (a) the shape list covers every lane; (b)+(c) the
# model-relative cvar bounds, one fold each; (d) the plain config's
# R.ok.  The heterogeneous layer GATES on the router -- it never
# re-states a routing rule.
def mc_ok(+shapes: List<&2, Nat>, +mps: List<&2, MProj>, +c: R.Config) -> Bool:
  Bool.and(Nat.is_eq(R.nats_len(shapes), R.nats_len(R.cfg_lanes(c))),
  Bool.and(mprojs_src_ok(shapes, mps),
  Bool.and(mprojs_tgt_ok(shapes, mps),
           R.ok(c))))

# --------------------------------------------------------------------------
# the per-lane SCHEME layer (SWEEP_LAWS_DESIGN.md, priority P3a): the
# config gains a per-lane SCHEME id -- WHICH INTEGRATOR each subnet runs.
#
# REPRESENTATION (the mconfig pattern, minimal): a PARALLEL list `schemes:
# List<&2, Nat>` keyed by lane, riding alongside shapes (the same
# parallel-list shape as mview's svs/tvs), plus the SCHEME TABLE -- a
# `List<&2, Nat>` whose length is the number of available schemes (the
# integrator itself is outside this layer's vocabulary; the table's length
# is the bound the validator enforces).  Defaults follow the nats_nth
# convention (0n past the end), but out-of-range reads are UNCALLABLE
# through scheme_ok: the length conjunct rejects a short list, the bounds
# conjunct rejects an id past the table.

# the per-lane bounds fold: every lane's scheme id is inside the scheme
# table (one is_lt per lane, the nats_lt_all / mprojs_src_ok fold shape)
def schemes_ok(+schemes: List<&2, Nat>, +ntab: Nat) -> Bool:
  match schemes:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(Nat.is_lt(h, ntab), schemes_ok(t, ntab))

# lane i's scheme id: entry i of the per-lane list (the nats_nth
# convention)
def lane_scheme(+schemes: List<&2, Nat>, +i: Nat) -> Nat:
  R.nats_nth(schemes, i)

# lane i's RESOLVED scheme: the table entry its id points at -- the
# routing the engine performs (lane i runs scheme schemes[i])
def scheme_of(+table: List<&2, Nat>, +schemes: List<&2, Nat>, +i: Nat) -> Nat:
  R.nats_nth(table, R.nats_nth(schemes, i))

# THE SCHEME VALIDATOR: mc_ok extended by the scheme dimension, three
# flat conjuncts:
#   (a) one scheme id per lane (the shape list's conjunct, one level
#       over: a short scheme list would silently default its missing
#       lanes to scheme 0);
#   (b) every id inside the table (the schemes_ok fold -- an
#       out-of-range id indexes past the integrator table);
#   (c) the base mc_ok -- the heterogeneous layer GATES on everything
#       below it, never re-states a rule.
def scheme_ok(+table: List<&2, Nat>, +schemes: List<&2, Nat>,
              +shapes: List<&2, Nat>, +mps: List<&2, MProj>,
              +c: R.Config) -> Bool:
  Bool.and(Nat.is_eq(R.nats_len(schemes), R.nats_len(R.cfg_lanes(c))),
  Bool.and(schemes_ok(schemes, R.nats_len(table)),
           mc_ok(shapes, mps, c)))
