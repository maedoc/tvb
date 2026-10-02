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
