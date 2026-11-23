#!/usr/bin/env bash
# Re-runnable check of the "no placeholder" claim:
#   1. no sorry / axiom / native_decide / implemented_by / unsafe / partial in the libraries;
#   2. the headline theorems depend only on Lean's three standard axioms
#      (propext, Classical.choice, Quot.sound), as printed by `#print axioms`.
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0
if grep -rnE '\bsorry\b|^\s*axiom\b|native_decide|implemented_by|^\s*unsafe\b|^\s*partial\b' \
    LeanCrdt LeanCrdt.lean LeanSync LeanSync.lean; then
  echo "FAIL: forbidden construct found (see above)"; fail=1
else
  echo "ok: no sorry/axiom/native_decide/implemented_by/unsafe/partial in LeanCrdt/ or LeanSync/"
fi
lake build >/dev/null || { echo "FAIL: lake build"; exit 1; }
out=$(lake env lean scripts/Axioms.lean 2>&1)
echo "$out"
n=$(grep -c "depends on axioms" <<<"$out")
bad=$(grep "depends on axioms" <<<"$out" | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" || true)
if [ "$n" -lt 22 ] || [ -n "$bad" ] || grep -q "sorryAx\|error" <<<"$out"; then
  echo "FAIL: unexpected axioms or errors"; fail=1
else
  echo "ok: $n headline theorems depend only on propext, Classical.choice, Quot.sound"
fi
exit $fail
