#!/usr/bin/env bash
# Router gate: proofs (kernel-verified), negative controls (must FAIL),
# functional tests (output pinned by #| lines, bend2 convention).
set -u
cd "$(dirname "$0")/.."
BEND="${BEND:-$HOME/.bend/bin/bend}"
fail=0

gate=$("$BEND" PROOF_router.bend --verdict 2>&1 | tail -1)
if [ "$gate" = "ALL PROOFS CHECK" ]; then
  echo "ok   PROOF_router.bend --verdict"
else
  echo "FAIL PROOF_router.bend --verdict"
  echo "$gate" | sed 's/^/     /'
  fail=1
fi

for f in bad/bad_*.bend; do
  if "$BEND" "$f" >/dev/null 2>&1; then
    echo "FAIL $f (negative control type-checked!)"
    fail=1
  else
    echo "ok   $f (rejected)"
  fi
done

cd tests
for f in *.bend; do
  want=$(grep '^#|' "$f" | sed 's/^#|//')
  got=$("$BEND" "$f" 2>&1)
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
