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

for f in bad/bad_wrap.bend bad/bad_json_time.bend; do
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
'ok=PASS lanes=1,2 projs=2 horizon=4
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
'ok=PASS lanes=2,3 projs=1 horizon=64
tick:  | i0=0 i1=0 num=1/2 win=0
tick:  | i0=0 i1=0 num=0/2 win=0
tick:  | i0=0 i1=0 num=1/2 win=0
tick:  | i0=0 i1=0 num=0/2 win=0
plateau (d=1+n+0 vs 1+n+9):  True
fresh   (i1<=newest):       True'

# 3. garbage text: refused at parse
run_case "json: garbage refused" \
  'not json at all!!!' \
'REJECTED: bad JSON or R.ok == False'

# 4. structurally valid JSON, invalid config (zero-period lane): refused by
#    R.ok -- the runtime gate the laws assume
run_case "json: zero-period lane refused by ok" \
  '{"lanes":[0,2],"projs":[],"horizon":1}' \
'REJECTED: bad JSON or R.ok == False'

rm -f "$bin"
[ "$fail" = 0 ] && echo "all green"
exit "$fail"
