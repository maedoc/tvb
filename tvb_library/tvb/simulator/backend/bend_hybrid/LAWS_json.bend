# LAWS_json.bend -- what the proofs guarantee for ARBITRARY JSON configs.
#
#   bend PROOF_json.bend            proofs checked
#   bend PROOF_json.bend --verdict  re-checked by the Lean-proved kernel
#
# The question this file answers: "the program is proofed and compiled --
# what survives the JSON that enters at RUNTIME?"  Answer: everything that
# is quantified over the full value space.  json_ingest.bend decodes ANY
# string (garbage included) into an ordinary R.Config, so a claim over
# `String` is a claim over every JSON document the binary will ever see.
#
# The headline property is the DELAY PLATEAU (read_saturate, and its
# per-config form json_delay_plateau): asking for a delay past the entire
# published history returns exactly the IC read -- and ALL such absurd
# delays return the SAME line.  The router SATURATES; it never wraps.  This
# is the precise difference from the engines' ring buffers, where a delay
# beyond the horizon ALIASES onto a recent slot (nb_hybrid's ValueError is
# aimed exactly at that aliasing).  Here, distinct in-history delays read
# distinct slots (read_fresh gives the bound), and distinct out-of-history
# delays collapse onto one point -- the IC.  No wrap-around exists to be
# confused by.
#
# Two instance laws pin the PARSER transcription (literal laws, tier 2 of
# the 3-tier division: laws pin structure/order, literals pin
# transcription, Python pins values).

import Base
import ./router.bend as R
import ./json_ingest.bend as J

# --------------------------------------------------------------------------
# 1. the leaf property: the delay plateau
# --------------------------------------------------------------------------

# Every delay of the form 1 + n + e (past the whole history of depth n)
# yields ONE line: the saturating read i0 = i1 = 0 (the IC slot).  Two
# consequences worth naming: (a) no wrap-around -- a ring buffer of size H
# would give delay d and d+H the SAME wrong slot, here d and d' > n give
# the same RIGHT slot; (b) the property needs no hypothesis -- it holds for
# every n, every fraction, every window, so for every projection of every
# config, decoded or not.
law read_saturate:
  for +n: Nat
  for +num: Nat
  for +den: Nat
  for +win: Nat
  for +e1: Nat
  for +e2: Nat
  {R.route_read(n, 1n+Nat.add(n, e1), num, den, win)
      == R.route_read(n, 1n+Nat.add(n, e2), num, den, win) : R.Line}

# --------------------------------------------------------------------------
# 2. the ingress property: the same, for every JSON string
# --------------------------------------------------------------------------

# For EVERY string s -- every JSON document, every typo, every fuzz input --
# every projection routed out of the decoded config after ANY number of
# ticks reads on the plateau.  This is read_saturate lifted through the
# decoder; its force is the quantifier: the compiled binary's runtime input
# cannot escape it.
law json_delay_plateau:
  for +s: String
  for +m: Nat
  for +e1: Nat
  for +e2: Nat
  {J.run_bump(J.json_decode(s), m, e1)
      == J.run_bump(J.json_decode(s), m, e2) : List<&2, R.Line>}

# --------------------------------------------------------------------------
# 3. instance laws: the parser transcribes
# --------------------------------------------------------------------------

# keys in order, one projection: decode is the identity on well-formed text
law json_decode_instance:
  {J.json_decode("{\"lanes\":[1,2],\"projs\":[[0,1,1,0,0]],\"horizon\":4}")
     == R.Config{1n <> 2n <> Nil{}, R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{}, 4n} : R.Config}

# garbage decodes to the empty default config -- still on the plateau
law json_decode_garbage:
  {J.json_decode("zz not json") == R.Config{Nil{}, Nil{}, 0n} : R.Config}

# --------------------------------------------------------------------------
# 4. the ok-conditioned capstone: every routed line of an ACCEPTED config
#    is FRESH, for every JSON string, at every tick
# --------------------------------------------------------------------------

# For every string s whose decoded config PASSES the validator, every routed
# read (all projections, any tick m) reads at or behind the newest published
# sample of its source lane: no read sees the future.  This composes the
# ok(cfg)=True law family (LAWS_router section 6) through the ingress fold:
# ok_lanes -> projs_ok_cons -> proj_src_bounded keep the lookup inside the
# lane list, and read_fresh (LAWS_router) closes each line.  The hypothesis
# is the validator the binary itself runs, so ACCEPTED input cannot escape.
law json_read_fresh:
  for +s: String
  for +m: Nat
  for +h: {R.ok(J.json_decode(s)) == True{} : Bool}
  {J.bumps_fresh(J.lanes_run(m, R.init_lanes(R.cfg_lanes(J.json_decode(s)))),
                 R.cfg_projs(J.json_decode(s)), 0n) == True{} : Bool}

# --------------------------------------------------------------------------
# 5. the COUPLING-FUNCTION config spec (see json_ingest.bend's cfun
#    section): pin the JSON -> data-structure mapping so a
#    mistranscription is UNSTATABLE.
# --------------------------------------------------------------------------
# Three fragile spots are pinned here, each by a tier-2 literal law (the
# kernel reduces both sides on literal configs):
#   (a) PARAMS ORDER: JSON cfun_params[i] lands in field i of the spec
#       (a transcription-adjacent copy-paste in the numba mako emission
#       is the historical bug class); one order law per kind with
#       nonempty params, tiny literals.
#   (b) KIND ROUTING: the JSON kind NAME -> table id (cfun_kind_of) and
#       the id -> row mapping (cfun_row carries the NAME back -- the
#       round trip is the tag); the junk id 11 exists and never validates.
#   (c) KIND-TABLE pins: APPLICATION POINT (pre = per-edge before the
#       weighted sum, post = after -- a mis-tag is silently wrong) and
#       ARITY (1 vs two-variable per-edge leaves like difference /
#       kuramoto) per kind.  The template's own dispatch is the truth
#       (nb-hybrid-sim.py.mako, verified 2026-10-07): note kuramoto_norm
#       (post, a*(1/N)*wsum) is a REAL kind the reference emits even
#       though a naive list stops at kuramoto.

# (b)+(c): the 11 table rows -- id -> (name, point, arity, nparams)
law cfun_table_linear:
  {J.cfun_row(0n) == J.CRow{"linear", False{}, 1n, 2n} : J.CRow}

law cfun_table_scaling:
  {J.cfun_row(1n) == J.CRow{"scaling", False{}, 1n, 1n} : J.CRow}

law cfun_table_sigmoidal:
  {J.cfun_row(2n) == J.CRow{"sigmoidal", False{}, 1n, 5n} : J.CRow}

law cfun_table_sigmoidal_jr:
  {J.cfun_row(3n) == J.CRow{"sigmoidal_jr", True{}, 2n, 5n} : J.CRow}

law cfun_table_sigmoidal_jr_legacy:
  {J.cfun_row(4n) == J.CRow{"sigmoidal_jr_legacy", True{}, 1n, 4n} : J.CRow}

law cfun_table_tanh:
  {J.cfun_row(5n) == J.CRow{"tanh", True{}, 1n, 4n} : J.CRow}

law cfun_table_difference:
  {J.cfun_row(6n) == J.CRow{"difference", True{}, 2n, 0n} : J.CRow}

law cfun_table_kuramoto:
  {J.cfun_row(7n) == J.CRow{"kuramoto", True{}, 2n, 0n} : J.CRow}

law cfun_table_pre_sigmoidal:
  {J.cfun_row(8n) == J.CRow{"pre_sigmoidal", True{}, 1n, 5n} : J.CRow}

law cfun_table_pre_sigmoidal_dynamic:
  {J.cfun_row(9n) == J.CRow{"pre_sigmoidal_dynamic", True{}, 2n, 6n} : J.CRow}

law cfun_table_kuramoto_norm:
  {J.cfun_row(10n) == J.CRow{"kuramoto_norm", False{}, 1n, 2n} : J.CRow}

# (b): the name -> id direction (the reference list, plus the junk id)
law cfun_name_linear:
  {J.cfun_kind_of("linear") == 0n : Nat}

law cfun_kind_unknown:
  {J.cfun_kind_of("frobnicate") == 11n : Nat}

# (a)+(c): one decode per kind with nonempty params -- params[i] lands in
# field i, and the record carries the kind's point/arity/nparams
law cfun_order_linear:
  {J.cfun_decode("{\"cfun_kind\":\"linear\",\"cfun_params\":[3,5]}")
     == J.CFun{0n, False{}, 1n, 3n, 5n, 0n, 0n, 0n, 0n, 2n, 2n, True{}} : J.CFun}

law cfun_order_scaling:
  {J.cfun_decode("{\"cfun_kind\":\"scaling\",\"cfun_params\":[3]}")
     == J.CFun{1n, False{}, 1n, 3n, 0n, 0n, 0n, 0n, 0n, 1n, 1n, True{}} : J.CFun}

law cfun_order_sigmoidal:
  {J.cfun_decode("{\"cfun_kind\":\"sigmoidal\",\"cfun_params\":[1,2,3,4,5]}")
     == J.CFun{2n, False{}, 1n, 1n, 2n, 3n, 4n, 5n, 0n, 5n, 5n, True{}} : J.CFun}

law cfun_order_sigmoidal_jr:
  {J.cfun_decode("{\"cfun_kind\":\"sigmoidal_jr\",\"cfun_params\":[1,2,3,4,5]}")
     == J.CFun{3n, True{}, 2n, 1n, 2n, 3n, 4n, 5n, 0n, 5n, 5n, True{}} : J.CFun}

law cfun_order_sigmoidal_jr_legacy:
  {J.cfun_decode("{\"cfun_kind\":\"sigmoidal_jr_legacy\",\"cfun_params\":[1,2,3,4]}")
     == J.CFun{4n, True{}, 1n, 1n, 2n, 3n, 4n, 0n, 0n, 4n, 4n, True{}} : J.CFun}

law cfun_order_tanh:
  {J.cfun_decode("{\"cfun_kind\":\"tanh\",\"cfun_params\":[1,2,3,4]}")
     == J.CFun{5n, True{}, 1n, 1n, 2n, 3n, 4n, 0n, 0n, 4n, 4n, True{}} : J.CFun}

law cfun_order_difference:
  {J.cfun_decode("{\"cfun_kind\":\"difference\",\"cfun_params\":[]}")
     == J.CFun{6n, True{}, 2n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, True{}} : J.CFun}

law cfun_order_kuramoto:
  {J.cfun_decode("{\"cfun_kind\":\"kuramoto\",\"cfun_params\":[]}")
     == J.CFun{7n, True{}, 2n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, True{}} : J.CFun}

law cfun_order_pre_sigmoidal:
  {J.cfun_decode("{\"cfun_kind\":\"pre_sigmoidal\",\"cfun_params\":[1,2,3,4,5]}")
     == J.CFun{8n, True{}, 1n, 1n, 2n, 3n, 4n, 5n, 0n, 5n, 5n, True{}} : J.CFun}

law cfun_order_pre_sigmoidal_dynamic:
  {J.cfun_decode("{\"cfun_kind\":\"pre_sigmoidal_dynamic\",\"cfun_params\":[1,2,3,4,5,6]}")
     == J.CFun{9n, True{}, 2n, 1n, 2n, 3n, 4n, 5n, 6n, 6n, 6n, True{}} : J.CFun}

law cfun_order_kuramoto_norm:
  {J.cfun_decode("{\"cfun_kind\":\"kuramoto_norm\",\"cfun_params\":[2,4]}")
     == J.CFun{10n, False{}, 1n, 2n, 4n, 0n, 0n, 0n, 0n, 2n, 2n, True{}} : J.CFun}

# the validator, pinned on four instances: good, wrong length, unknown
# kind, garbage
law cf_ok_good:
  {J.cf_ok(J.cfun_decode("{\"cfun_kind\":\"linear\",\"cfun_params\":[3,5]}")) == True{} : Bool}

law cf_ok_len_wrong:
  {J.cf_ok(J.cfun_decode("{\"cfun_kind\":\"linear\",\"cfun_params\":[1,2,3]}")) == False{} : Bool}

law cf_ok_kind_unknown:
  {J.cf_ok(J.cfun_decode("{\"cfun_kind\":\"frobnicate\",\"cfun_params\":[1,2]}")) == False{} : Bool}

law cf_ok_junk:
  {J.cf_ok(J.cfun_decode("zz not json")) == False{} : Bool}

# (d) the validator's and-eliminations: an ACCEPTED spec is in-table,
# length-exact and parse-clean (Bool form, the shape the runtime gates on)
law cf_ok_in_table:
  for +c: J.CFun
  for +h: {J.cf_ok(c) == True{} : Bool}
  {Nat.is_lt(J.c_kind(c), 11n) == True{} : Bool}

law cf_ok_len_matches:
  for +c: J.CFun
  for +h: {J.cf_ok(c) == True{} : Bool}
  {Nat.is_eq(J.c_plen(c), J.c_nparams(c)) == True{} : Bool}

law cf_ok_parse_valid:
  for +c: J.CFun
  for +h: {J.cf_ok(c) == True{} : Bool}
  {J.c_valid(c) == True{} : Bool}

# (e) THE CFUN CONTRACT -- the capstone in the json_named_contract
# pair-equality shape: for EVERY string whose decoded spec passes the
# validator, all three validator conjuncts hold (in-table kind, exact
# params length against the kind table, clean parse).  Together with the
# order laws, an ACCEPTED cfun section is a table row: the JSON kind is
# a real kind, its params array is exactly the kind's params.
law json_cfun_contract:
  for +s: String
  for +h: {J.cf_ok(J.cfun_decode(s)) == True{} : Bool}
  {(Nat.is_lt(J.c_kind(J.cfun_decode(s)), 11n),
    Nat.is_eq(J.c_plen(J.cfun_decode(s)), J.c_nparams(J.cfun_decode(s))),
    J.c_valid(J.cfun_decode(s)))
   == (True{}, True{}, True{}) : Bool & (Bool & Bool)}
