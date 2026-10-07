#!/usr/bin/env bash
# Mons gate: proofs (kernel-verified), the rate-0 negative control (must
# FAIL), the functional smoke test (output pinned by #| lines).  Modeled
# on tests/run_sweep.sh; covers only this layer's files.
set -u
cd "$(dirname "$0")/.."
BEND="${BEND:-$HOME/.bend/bin/bend}"
export PATH="$HOME/.local/bin:$PATH"
fail=0

gate=$("$BEND" PROOF_mons.bend --verdict 2>&1 | grep -v 'bend 2' | tail -1)
if [ "$gate" = "ALL PROOFS CHECK" ]; then
  echo "ok   PROOF_mons.bend --verdict"
else
  echo "FAIL PROOF_mons.bend --verdict"
  echo "$gate" | sed 's/^/     /'
  fail=1
fi

for f in bad/bad_mon_rate.bend; do
  if "$BEND" "$f" >/dev/null 2>&1; then
    echo "FAIL $f (negative control type-checked!)"
    fail=1
  else
    echo "ok   $f (rejected)"
  fi
done

cd tests
for f in mons_smoke.bend; do
  want=$(grep '^#|' "$f" | sed 's/^#|//')
  got=$("$BEND" "$f" 2>&1 | grep -v 'bend 2')
  if [ "$got" = "$want" ]; then
    echo "ok   $f"
  else
    echo "FAIL $f"
    diff <(printf '%s\n' "$want") <(printf '%s\n' "$got") | sed 's/^/     /'
    fail=1
  fi
done

[ "$fail" = 0 ] && echo "all green"
exit "$fail"
