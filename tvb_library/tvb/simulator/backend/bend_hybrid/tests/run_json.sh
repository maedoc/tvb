#!/usr/bin/env bash
# JSON-ingress gate: proofs (kernel-verified), negative controls (must
# FAIL), and the compiled binary ingesting ARBITRARY JSON at runtime
# (outputs pinned below).
#
#   tests/run_json.sh
#
# Companion to tests/run_router.sh (which owns the router laws proper).
set -u
cd "$(dirname "$0")/.."
BEND="${BEND:-$HOME/.bend/bin/bend}"
export PATH="$HOME/.local/bin:$PATH"   # lean, for --verdict
fail=0

gate=$("$BEND" PROOF_json.bend --verdict 2>&1 | grep -v 'bend 2' | tail -1)
if [ "$gate" = "ALL PROOFS CHECK" ]; then
  echo "ok   PROOF_json.bend --verdict"
else
  echo "FAIL PROOF_json.bend --verdict"
  echo "$gate" | sed 's/^/     /'
  fail=1
fi

for f in bad/bad_wrap.bend bad/bad_json_time.bend bad/bad_cfun_spec.bend; do
  if "$BEND" "$f" >/dev/null 2>&1; then
    echo "FAIL $f (negative control type-checked!)"
    fail=1
  else
    echo "ok   $f (rejected)"
  fi
done

bin=$(mktemp -t json_demo.XXXXXX)
if ! "$BEND" json_demo.bend -o "$bin" >/dev/null 2>&1; then
  echo "FAIL json_demo.bend does not compile"
  rm -f "$bin"
  exit 1
fi

run_case() {
  local name="$1" json="$2" want="$3"
  local got
  got=$("$bin" -- "$json" 2>&1)
  if [ "$got" = "$want" ]; then
    echo "ok   $name"
  else
    echo "FAIL $name"
    diff <(printf '%s\n' "$want") <(printf '%s\n' "$got") | sed 's/^/     /'
    fail=1
  fi
}

# 1. the multi-rate config, keys in order: every routed index pinned
run_case "json: multi-rate (pinned ticks)" \
  '{"lanes":[1,2],"projs":[[0,1,1,0,0],[1,0,2,1,0]],"horizon":4}' \
'sweep: names=0 cols=0 ns=0
named: lanes=2 models=0 projs=2 svars=0 tcvars=0 ok=False
ok=PASS lanes=1,2 projs=2 horizon=4
tick:  | i0=0 i1=1 num=0/1 win=0 | i0=0 i1=0 num=1/2 win=1
tick:  | i0=1 i1=2 num=0/1 win=0 | i0=0 i1=0 num=0/2 win=1
tick:  | i0=2 i1=3 num=0/1 win=0 | i0=0 i1=0 num=1/2 win=1
tick:  | i0=3 i1=4 num=0/1 win=0 | i0=0 i1=1 num=0/2 win=1
plateau (d=1+n+0 vs 1+n+9):  True True
fresh   (i1<=newest):       True'

# 2. keys shuffled, whitespace, a delay of 50 on a ~2-sample history: the
#    saturating read (every line is the IC read {0,0}) on an ACCEPTED config
run_case "json: shuffled keys + over-history delay" \
  '{ "projs" : [ [ 0 , 1 , 50 , 0 , 0 ] ] , "horizon" : 64 , "lanes" : [ 2 , 3 ] }' \
'sweep: names=0 cols=0 ns=0
named: lanes=2 models=0 projs=1 svars=0 tcvars=0 ok=False
ok=PASS lanes=2,3 projs=1 horizon=64
tick:  | i0=0 i1=0 num=1/2 win=0
tick:  | i0=0 i1=0 num=0/2 win=0
tick:  | i0=0 i1=0 num=1/2 win=0
tick:  | i0=0 i1=0 num=0/2 win=0
plateau (d=1+n+0 vs 1+n+9):  True
fresh   (i1<=newest):       True'

# 3. garbage text: refused at parse
run_case "json: garbage refused" \
  'not json at all!!!' \
'sweep: names=0 cols=0 ns=0
named: lanes=0 models=0 projs=0 svars=0 tcvars=0 ok=False
REJECTED: bad JSON or the named validator == False'

# 4. structurally valid JSON, invalid config (zero-period lane): refused by
#    R.ok -- the runtime gate the laws assume
run_case "json: zero-period lane refused by ok" \
  '{"lanes":[0,2],"projs":[],"horizon":1}' \
'sweep: names=0 cols=0 ns=0
named: lanes=2 models=0 projs=0 svars=0 tcvars=0 ok=False
REJECTED: bad JSON or the named validator == False'

# 5. a sweep table on argv: the total sweep decode is visible even though
#    the string carries no config (no lanes key), so the gate refuses it
run_case "json: sweep table decoded (then refused, no config)" \
  '{"sweep_names":["coupling_scale"],"sweep_cols":[[2000,2100]]}' \
'sweep: names=1 cols=1 ns=2
named: lanes=0 models=0 projs=0 svars=0 tcvars=0 ok=False
REJECTED: bad JSON or the named validator == False'

# 6. the NAMED-CONFIG ingress: the heterogeneous demo network (JansenRit +
#    FHN name lists, named projection 'y1' -> 'xi') -- the named validator
#    accepts and the binary runs the DECODED config (the plain gate
#    refuses: the named keys junk the plain parse)
run_case "json: named config (pinned ticks)" \
  '{"lanes":[1,2],"projs":[[0,1,1,0,0]],"horizon":4,"svar_names":[["y0","y1","y2","y3","y4","y5"],["xi","eta","alpha","beta"]],"proj_svars":["y1"],"proj_tcvars":["xi"]}' \
'sweep: names=0 cols=0 ns=0
named: lanes=2 models=2 projs=1 svars=1 tcvars=1 ok=True
ok=PASS lanes=1,2 projs=1 horizon=4
tick:  | i0=0 i1=1 num=0/1 win=0
tick:  | i0=1 i1=2 num=0/1 win=0
tick:  | i0=2 i1=3 num=0/1 win=0
tick:  | i0=3 i1=4 num=0/1 win=0
plateau (d=1+n+0 vs 1+n+9):  True
fresh   (i1<=newest):       True'

# 7. a named config with an UNKNOWN cvar name ('zz' is in no model's name
#    list): find_name lands on the junk index, mc_ok rejects -- refused
run_case "json: named config, unknown cvar name refused" \
  '{"lanes":[1,2],"projs":[[0,1,1,0,0]],"horizon":4,"svar_names":[["y0","y1","y2","y3","y4","y5"],["xi","eta","alpha","beta"]],"proj_svars":["zz"],"proj_tcvars":["xi"]}' \
'sweep: names=0 cols=0 ns=0
named: lanes=2 models=2 projs=1 svars=1 tcvars=1 ok=False
REJECTED: bad JSON or the named validator == False'

rm -f "$bin"
[ "$fail" = 0 ] && echo "all green"
exit "$fail"
