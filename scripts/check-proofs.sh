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
def quote : Char := '"'
def prime' : Char := '\''
theorem bad5 : True := by sorry
LEAN
hits=$(scripts/check-forbidden.sh "$tmp" | wc -l)
rm -rf "$tmp"
if [ "$hits" -ne 5 ]; then
  echo "FAIL: forbidden-construct self-test found $hits of 5 planted constructs"; fail=1
else
  echo "ok: forbidden-construct self-test (5 of 5 planted constructs found; comments, strings and"
  echo "    character literals such as '\"' ignored)"
fi
if scripts/check-forbidden.sh LeanCrdt LeanCrdt.lean LeanSync LeanSync.lean; then
  echo "ok: no sorry/axiom/native_decide/implemented_by/unsafe/partial in LeanCrdt/ or LeanSync/"
else
  echo "FAIL: forbidden construct found (see above)"; fail=1
fi

# Lean's own evidence, independent of the scanner: the build must not report any `sorry`.
# Self-test the pattern on a file that does use `sorry`, then check the build log (Lake replays
# the warnings of cached modules, so this covers every module of the build).
tmp=$(mktemp -d)
printf 'theorem t : True := by sorry\n' > "$tmp/S.lean"
if lake env lean "$tmp/S.lean" 2>&1 | grep -q "declaration uses .sorry."; then
  echo "ok: sorry-warning pattern self-test"
else
  echo "FAIL: the sorry-warning pattern does not match Lean's warning"; fail=1
fi
rm -rf "$tmp"
blog=$(lake build 2>&1) || { echo "$blog" | tail -20; echo "FAIL: lake build"; exit 1; }
if grep -q "declaration uses .sorry." <<<"$blog"; then
  grep "declaration uses .sorry." <<<"$blog"
  echo "FAIL: lake build reports a declaration that uses sorry"; fail=1
else
  echo "ok: lake build reports no declaration that uses sorry"
fi
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
