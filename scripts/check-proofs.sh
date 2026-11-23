#!/usr/bin/env bash
# Re-runnable check of the "no placeholder" claim:
#   1. no sorry / axiom / native_decide / implemented_by / unsafe / partial anywhere in the
#      libraries outside comments (scripts/check-forbidden.sh), after a self-test of that check;
#   2. every theorem listed in scripts/Axioms.lean reports its axioms, and every axiom reported is
#      one of Lean's standard three (propext, Classical.choice, Quot.sound). Fewer (or none) is fine.
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0

# self-test: the forbidden-construct check must catch constructs that are not at the line start
tmp=$(mktemp -d)
cat > "$tmp/T.lean" <<'LEAN'
/-- a partial blob, sorry -/
def ok := "unsafe partial"   -- partial
private partial def bad1 : Nat → Nat := fun n => n
@[inline] unsafe def bad2 := 1
protected axiom bad3 : True
theorem bad4 : True := by sorry
LEAN
hits=$(scripts/check-forbidden.sh "$tmp" | wc -l)
rm -rf "$tmp"
if [ "$hits" -ne 4 ]; then
  echo "FAIL: forbidden-construct self-test found $hits of 4 planted constructs"; fail=1
else
  echo "ok: forbidden-construct self-test (4 of 4 planted constructs found, comments and strings ignored)"
fi
if scripts/check-forbidden.sh LeanCrdt LeanCrdt.lean LeanSync LeanSync.lean; then
  echo "ok: no sorry/axiom/native_decide/implemented_by/unsafe/partial in LeanCrdt/ or LeanSync/"
else
  echo "FAIL: forbidden construct found (see above)"; fail=1
fi

lake build >/dev/null || { echo "FAIL: lake build"; exit 1; }
out=$(lake env lean scripts/Axioms.lean 2>&1)
echo "$out"
expected=$(grep -c '^#print axioms' scripts/Axioms.lean)
reports=$(grep -cE "depends on axioms: \[|does not depend on any axioms" <<<"$out")
bad=$(grep -oE "depends on axioms: \[[^]]*\]" <<<"$out" | sed -E 's/.*\[(.*)\]/\1/' | tr ',' '\n' \
      | sed -E 's/^ +| +$//g' | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ "$reports" -ne "$expected" ]; then
  echo "FAIL: $reports axiom reports for $expected '#print axioms' lines"; fail=1
elif [ -n "$bad" ] || grep -qE "error|sorryAx" <<<"$out"; then
  echo "FAIL: axioms outside the allowlist, or errors: $bad"; fail=1
else
  echo "ok: $expected headline theorems use no axioms beyond propext, Classical.choice, Quot.sound"
fi
exit $fail
