#!/usr/bin/env bash
# Sweep gate: proofs (kernel-verified), the width negative control (must
# FAIL), the functional smoke test (output pinned by #| lines).  Modeled
# on tests/run_router.sh; covers only this layer's files.
set -u
cd "$(dirname "$0")/.."
BEND="${BEND:-$HOME/.bend/bin/bend}"
export PATH="$HOME/.local/bin:$PATH"
fail=0

gate=$("$BEND" PROOF_sweep.bend --verdict 2>&1 | grep -v 'bend 2' | tail -1)
if [ "$gate" = "ALL PROOFS CHECK" ]; then
  echo "ok   PROOF_sweep.bend --verdict"
else
  echo "FAIL PROOF_sweep.bend --verdict"
  echo "$gate" | sed 's/^/     /'
  fail=1
fi

for f in bad/bad_sweep_width.bend bad/bad_sweep_rowshape.bend \
         bad/bad_sweep_csr.bend bad/bad_seed.bend; do
  if "$BEND" "$f" >/dev/null 2>&1; then
    echo "FAIL $f (negative control type-checked!)"
    fail=1
  else
    echo "ok   $f (rejected)"
  fi
done

cd tests
for f in sweep_smoke.bend; do
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
