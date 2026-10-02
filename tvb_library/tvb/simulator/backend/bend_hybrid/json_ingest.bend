# json_ingest.bend -- JSON ingress for the router: parse a JSON config
# document into R.Config values AT RUNTIME, inside the compiled binary.
#
# This closes the loop on "what do the proofs say about arbitrary runtime
# configs?": the binary accepts JSON text on its command line, decodes it
# here, runs R.ok on the decoded config (the binary refuses on False), and
# only then routes.  The decoder is TOTAL -- any string, including garbage,
# yields an R.Config (junk parses to an invalid JCfg that json_good
# rejects) -- so the law `json_delay_plateau` in LAWS_json.bend can
# quantify over ALL strings and still say something about every config the
# binary will ever execute.
#
# Schema (whitespace-tolerant, keys in ANY order):
#   {"lanes":[k0,k1,...],"projs":[[src,tgt,d,win,tc],...],"horizon":h}
# A strict JSON subset: no escapes inside strings, keys are bare words,
# numbers are decimal Nats.  Anything else is parse-invalid.
#
# Bend discipline observed here (see NOTES.md): one match per def; matches
# inspect only parameters and pattern bindings; no forward references and
# no mutual recursion -- so the parser is ONE self-recursive state machine
# (obj_go: multi-scrutinee `match ts mode:` with flat multi-cons token
# patterns) plus pure helpers that return DATA and never call back.  The
# tokenizer is the same shape.

import Base
import ./router.bend as R

# --------------------------------------------------------------------------
# char classification (runtime only -- U32 primitives do not reduce on
# symbolic args, which is fine: the LAWS quantify over DECODED values, not
# over the text)
# --------------------------------------------------------------------------

def cls_ws(+x: U32) -> Bool:
  Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 9),
  Bool.or(U32.is_eq(x, 10), U32.is_eq(x, 13))))

def cls_dig(+x: U32) -> Bool:
  Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))

def digit_val(c: Char) -> Maybe<&2, Nat>:
  match c:
    case Chr{+x}:
      Bool.pick(Maybe<&2, Nat>, cls_dig(x), Some{U32.to_nat((x - 48 : U32))}, None{})

# class codes: 0 ws, 1 '{', 2 '}', 3 '[', 4 ']', 5 ',', 6 ':', 7 '"',
# 8 digit, 9 other
def char_cls(c: Char) -> Nat:
  match c:
    case Chr{+x}:
      Bool.pick(Nat, cls_ws(x), 0n,
      Bool.pick(Nat, U32.is_eq(x, 123), 1n,
      Bool.pick(Nat, U32.is_eq(x, 125), 2n,
      Bool.pick(Nat, U32.is_eq(x, 91), 3n,
      Bool.pick(Nat, U32.is_eq(x, 93), 4n,
      Bool.pick(Nat, U32.is_eq(x, 44), 5n,
      Bool.pick(Nat, U32.is_eq(x, 58), 6n,
      Bool.pick(Nat, U32.is_eq(x, 34), 7n,
      Bool.pick(Nat, cls_dig(x), 8n, 9n)))))))))

# --------------------------------------------------------------------------
# tokens
# --------------------------------------------------------------------------

type Tok is Data:
  TBraceO{}
  TBraceC{}
  TBrackO{}
  TBrackC{}
  TComma{}
  TColon{}
  TNum{val: Nat}
  TStr{val: String}
  TBad{}

# tokenizer state, threaded WHOLE through helpers
type St is Data:
  St{num: Maybe<&2, Nat>, str: Maybe<&2, String>, acc: List<&2, Tok>}

def st_num(s: St) -> Maybe<&2, Nat>:
  match s:
    case St{num, str, acc}:
      num

def st_str(s: St) -> Maybe<&2, String>:
  match s:
    case St{num, str, acc}:
      str

def st_acc(s: St) -> List<&2, Tok>:
  match s:
    case St{num, str, acc}:
      acc

def toks_rev(xs: List<&2, Tok>, acc: List<&2, Tok>) -> List<&2, Tok>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      toks_rev(t, h <> acc)

def nats_rev(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      nats_rev(t, h <> acc)

def projs_rev(xs: List<&2, R.Proj>, acc: List<&2, R.Proj>) -> List<&2, R.Proj>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      projs_rev(t, h <> acc)

def num_flush(num: Maybe<&2, Nat>, acc: List<&2, Tok>) -> List<&2, Tok>:
  match num:
    case Some{value}:
      TNum{value} <> acc
    case _:
      acc

def num_mul(pend: Maybe<&2, Nat>, d: Nat) -> Nat:
  match pend:
    case Some{value}:
      Nat.add(Nat.mul(value, 10n), d)
    case _:
      d

def num_add(d: Maybe<&2, Nat>, +st: St) -> St:
  match d:
    case Some{value}:
      St{Some{num_mul(st_num(st), value)}, st_str(st), st_acc(st)}
    case _:
      st

# flush a pending number, then push one token
def flush_st(+st: St, tok: Tok) -> St:
  St{None{}, st_str(st), tok <> num_flush(st_num(st), st_acc(st))}

# flush a pending number and push nothing
def flush_only(+st: St) -> St:
  St{None{}, st_str(st), num_flush(st_num(st), st_acc(st))}

# one char INSIDE a string: a quote closes it, anything else extends it
def in_quote(b: Bool, buf: String, h: Char, +st: St) -> St:
  match b:
    case True{}:
      St{None{}, None{}, TStr{buf} <> num_flush(st_num(st), st_acc(st))}
    case _:
      St{None{}, Some{String.append(buf, SCon{h, SNil{}})}, st_acc(st)}

# one char outside a string, by class
def out_cls(k: Nat, d: Maybe<&2, Nat>, +st: St) -> St:
  match k:
    case 0n:
      flush_only(st)
    case 1n:
      flush_st(st, TBraceO{})
    case 2n:
      flush_st(st, TBraceC{})
    case 3n:
      flush_st(st, TBrackO{})
    case 4n:
      flush_st(st, TBrackC{})
    case 5n:
      flush_st(st, TComma{})
    case 6n:
      flush_st(st, TColon{})
    case 7n:
      St{None{}, Some{SNil{}}, num_flush(st_num(st), st_acc(st))}
    case 8n:
      num_add(d, st)
    case _:
      flush_st(st, TBad{})

def step_in(sm: Maybe<&2, String>, k: Nat, d: Maybe<&2, Nat>, h: Char, +st: St) -> St:
  match sm:
    case Some{value}:
      in_quote(Nat.is_eq(k, 7n), value, h, st)
    case _:
      out_cls(k, d, st)

def tok_step(k: Nat, d: Maybe<&2, Nat>, h: Char, +st: St) -> St:
  step_in(st_str(st), k, d, h, st)

def tok_go(s: String, +st: St) -> List<&2, Tok>:
  match s:
    case SNil{}:
      toks_rev(num_flush(st_num(st), st_acc(st)), Nil{})
    case SCon{+h, t}:
      tok_go(t, tok_step(char_cls(h), digit_val(h), h, st))

def tokens(s: String) -> List<&2, Tok>:
  tok_go(s, St{None{}, None{}, Nil{}})

# --------------------------------------------------------------------------
# the parse accumulator
# --------------------------------------------------------------------------

type JCfg is Data:
  JCfg{lanes: List<&2, Nat>, projs: List<&2, R.Proj>, horizon: Nat, seen: Nat, valid: Bool}

def j_lanes(+jc: JCfg) -> List<&2, Nat>:
  match jc:
    case JCfg{lanes, projs, horizon, seen, valid}:
      lanes

def j_projs(+jc: JCfg) -> List<&2, R.Proj>:
  match jc:
    case JCfg{lanes, projs, horizon, seen, valid}:
      projs

def j_horizon(+jc: JCfg) -> Nat:
  match jc:
    case JCfg{lanes, projs, horizon, seen, valid}:
      horizon

def j_valid(+jc: JCfg) -> Bool:
  match jc:
    case JCfg{lanes, projs, horizon, seen, valid}:
      valid

def jc_set_lanes(+jc: JCfg, vals: List<&2, Nat>) -> JCfg:
  match jc:
    case JCfg{lanes, projs, horizon, seen, valid}:
      JCfg{vals, projs, horizon, 1n+seen, valid}

def jc_set_projs(+jc: JCfg, vals: List<&2, R.Proj>) -> JCfg:
  match jc:
    case JCfg{lanes, projs, horizon, seen, valid}:
      JCfg{lanes, vals, horizon, 1n+seen, valid}

def jc_set_horizon(+jc: JCfg, val: Nat) -> JCfg:
  match jc:
    case JCfg{lanes, projs, horizon, seen, valid}:
      JCfg{lanes, projs, val, 1n+seen, valid}

def jc_bad(+jc: JCfg) -> JCfg:
  match jc:
    case JCfg{lanes, projs, horizon, seen, valid}:
      JCfg{lanes, projs, horizon, seen, False{}}

def jc_mark(b: Bool, +jc: JCfg) -> JCfg:
  match b:
    case True{}:
      jc
    case _:
      jc_bad(jc)

def jc_done(b: Bool, lanes: List<&2, Nat>, projs: List<&2, R.Proj>, horizon: Nat) -> JCfg:
  match b:
    case True{}:
      JCfg{lanes, projs, horizon, 3n, True{}}
    case _:
      JCfg{lanes, projs, horizon, 0n, False{}}

# a closed object is valid iff nothing junk'd AND all three keys were seen
def jc_final(+jc: JCfg) -> JCfg:
  match jc:
    case JCfg{lanes, projs, horizon, seen, valid}:
      jc_done(Bool.and(valid, Nat.is_eq(seen, 3n)), lanes, projs, horizon)

def jc_cfg(+jc: JCfg) -> R.Config:
  R.Config{j_lanes(jc), j_projs(jc), j_horizon(jc)}

# --------------------------------------------------------------------------
# pure parse helpers: they return DATA and never call back into a spine
# --------------------------------------------------------------------------

# "lanes" -> mode 1, "projs" -> mode 2, anything else -> mode 9 (junk)
def key_arr_mode(+key: String) -> Nat:
  Bool.pick(Nat, String.eq(key, "lanes"), 1n,
  Bool.pick(Nat, String.eq(key, "projs"), 2n, 9n))

# a number is a value only for "horizon"
def jc_num_field(+key: String, val: Nat, +jc: JCfg) -> JCfg:
  Bool.pick(JCfg, String.eq(key, "horizon"), jc_set_horizon(jc, val), jc_bad(jc))

# exactly five numbers make one projection [src, tgt, d, win, tc]; tacc
# accumulated them prepended, so the pattern binds them right to left
def proj_ok(tacc: List<&2, Nat>) -> Bool:
  match tacc:
    case e <> d <> c <> b <> a <> Nil{}:
      True{}
    case _:
      False{}

def proj_push(tacc: List<&2, Nat>, pacc: List<&2, R.Proj>) -> List<&2, R.Proj>:
  match tacc:
    case e <> d <> c <> b <> a <> Nil{}:
      R.Proj{a, b, c, d, e} <> pacc
    case _:
      pacc

# end of input (or '}'): only mode 0 (object level) is a clean end
def jc_end(m: Nat, +jc: JCfg) -> JCfg:
  match m:
    case 0n:
      jc_final(jc)
    case _:
      jc_bad(jc)

# --------------------------------------------------------------------------
# the object parser: ONE self-recursive state machine over (tokens, mode).
# modes: 0 object level, 1 inside the lanes array, 2 inside the projs
# array, 3 inside one projection tuple, 9 junk.  Flat multi-cons token
# patterns handle "key": value introductions in one arm.
# --------------------------------------------------------------------------

def obj_go(ts: List<&2, Tok>, m: Nat, key: String, +tacc: List<&2, Nat>,
           lacc: List<&2, Nat>, pacc: List<&2, R.Proj>, jc: JCfg) -> JCfg:
  match ts m:
    case Nil{} _:
      jc_end(m, jc)
    case TBraceO{} <> t 0n:
      obj_go(t, 0n, key, tacc, lacc, pacc, jc)
    case TComma{} <> t 0n:
      obj_go(t, 0n, key, tacc, lacc, pacc, jc)
    case TBraceC{} <> t 0n:
      jc_end(0n, jc)
    case TStr{+k2} <> TColon{} <> TBrackO{} <> t 0n:
      obj_go(t, key_arr_mode(k2), k2, Nil{}, lacc, pacc, jc)
    case TStr{+k2} <> TColon{} <> TNum{val} <> t 0n:
      obj_go(t, 0n, k2, Nil{}, lacc, pacc, jc_num_field(k2, val, jc))
    case TNum{val} <> t 1n:
      obj_go(t, 1n, key, tacc, val <> lacc, pacc, jc)
    case TComma{} <> t 1n:
      obj_go(t, 1n, key, tacc, lacc, pacc, jc)
    case TBrackC{} <> t 1n:
      obj_go(t, 0n, key, tacc, Nil{}, pacc, jc_set_lanes(jc, nats_rev(lacc, Nil{})))
    case TBrackO{} <> t 2n:
      obj_go(t, 3n, key, Nil{}, lacc, pacc, jc)
    case TComma{} <> t 2n:
      obj_go(t, 2n, key, tacc, lacc, pacc, jc)
    case TBrackC{} <> t 2n:
      obj_go(t, 0n, key, tacc, lacc, Nil{}, jc_set_projs(jc, projs_rev(pacc, Nil{})))
    case TNum{val} <> t 3n:
      obj_go(t, 3n, key, val <> tacc, lacc, pacc, jc)
    case TComma{} <> t 3n:
      obj_go(t, 3n, key, tacc, lacc, pacc, jc)
    case TBrackC{} <> t 3n:
      obj_go(t, 2n, key, Nil{}, lacc, proj_push(tacc, pacc), jc_mark(proj_ok(tacc), jc))
    case _ _:
      jc_bad(jc)

def obj_parse(ts: List<&2, Tok>) -> JCfg:
  obj_go(ts, 0n, SNil{}, Nil{}, Nil{}, Nil{}, JCfg{Nil{}, Nil{}, 0n, 0n, True{}})

# --------------------------------------------------------------------------
# the ingress surface
# --------------------------------------------------------------------------

# TOTAL decode: any string at all yields a Config (junk -> empty default).
# This totality is what lets json_delay_plateau quantify over ALL strings.
def json_decode(s: String) -> R.Config:
  jc_cfg(obj_parse(tokens(s)))

# the runtime gate: parse-valid AND R.ok -- the binary runs nothing else
def json_good(+s: String) -> Bool:
  Bool.and(j_valid(obj_parse(tokens(s))), R.ok(json_decode(s)))

# --------------------------------------------------------------------------
# spec-level helpers shared by LAWS_json.bend and the runtime demo: a run
# of m ticks over the decoded config, with every projection's delay BUMPED
# past the whole published history (d = 1 + newest + e) -- the saturating
# read
# --------------------------------------------------------------------------

def lanes_run(m: Nat, +ls: List<&2, R.Lane>) -> List<&2, R.Lane>:
  match m:
    case 0n:
      ls
    case 1n+p:
      lanes_run(p, R.lanes_step(ls))

def route_bump(+ls: List<&2, R.Lane>, +p: R.Proj, +e: Nat) -> R.Line:
  R.route_read(R.lane_newest(R.nth_lane(ls, R.proj_src(p))),
               1n+Nat.add(R.lane_newest(R.nth_lane(ls, R.proj_src(p))), e),
               R.lane_num(R.nth_lane(ls, R.proj_src(p))),
               R.lane_k(R.nth_lane(ls, R.proj_src(p))),
               R.proj_win(p))

def routes_bump(+ls: List<&2, R.Lane>, ps: List<&2, R.Proj>, +e: Nat) -> List<&2, R.Line>:
  match ps:
    case Nil{}:
      Nil{}
    case h <> t:
      route_bump(ls, h, e) <> routes_bump(ls, t, e)

def run_bump(+c: R.Config, m: Nat, +e: Nat) -> List<&2, R.Line>:
  routes_bump(lanes_run(m, R.init_lanes(R.cfg_lanes(c))), R.cfg_projs(c), e)
