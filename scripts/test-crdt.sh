#!/usr/bin/env bash
# Build the library (which checks every proof) and run the native CRDT tests, including the
# stack-depth test. Exit status is non-zero on any failure.
#
# Stack test. Compiled Lean runs `main` on a thread whose stack is LEAN_STACK_SIZE_KB
# (+128 KB runtime buffer; default 1 GB). We set it to STACK_KB and require:
#   1. calibration: a trivial non-tail recursion of depth 13,000 (the spike's measured browser
#      budget, ~13k frames in Node) must crash -> the native budget is no larger than the browser's;
#   2. control: the non-tail-recursive *specification* of the merge, on the scale test's sizes,
#      must crash -> the scale test would catch the recursion pattern we are guarding against;
#   3. the 20,000-path scale test, the unit tests and the simulation must pass under that stack.
# Caveat: native and wasm frame sizes differ; the calibration is in frames of a trivial function.
set -uo pipefail
ulimit -c 0  # the expected overflows abort(); do not leave core dumps behind
cd "$(dirname "$0")/.."

STACK_KB=${STACK_KB:-256}
BIN=.lake/build/bin/crdt-tests
fail=0

blog=$(lake build 2>&1) || { echo "$blog"; exit 1; }
echo "$blog" | tail -1
if grep -q "declaration uses .sorry." <<<"$blog"; then
  echo "FAIL: lake build reports a declaration that uses sorry"; fail=1
fi
lake build crdt-tests || exit 1

if scripts/check-forbidden.sh LeanCrdt LeanCrdt.lean LeanSync LeanSync.lean; then
  echo "ok: no sorry/axiom/native_decide/implemented_by/unsafe/partial in LeanCrdt/ or LeanSync/ (outside comments)"
else
  echo "FAIL: forbidden construct found in LeanCrdt/ or LeanSync/"; fail=1
fi

echo "== full tests, default stack"
"$BIN" all || fail=1

echo "== stack test, LEAN_STACK_SIZE_KB=$STACK_KB"
# Run under the small stack; succeed only if the run died the way a Lean stack overflow does:
# SIGABRT (exit status 134) *and* the runtime's "Stack overflow detected" diagnostic on stderr.
# Any other failure (usage error, panic, wrong exit code) is NOT an overflow.
last_rc=0
overflowed() {
  local err
  err=$( { LEAN_STACK_SIZE_KB=$STACK_KB "$BIN" "$@" >/dev/null; } 2>&1 )
  last_rc=$?
  [ "$last_rc" -eq 134 ] && grep -q "Stack overflow detected" <<<"$err"
}
expect_crash() {
  if overflowed "$@"; then
    echo "ok: '$*' overflowed as expected"
  else
    echo "FAIL: '$*' did not die of a stack overflow (exit $last_rc): the calibration did not run or the limit is not tight enough"; fail=1
  fi
}
expect_pass() {
  if LEAN_STACK_SIZE_KB=$STACK_KB "$BIN" "$@" > /dev/null; then
    echo "ok: '$*' passed under the small stack"
  else
    echo "FAIL: '$*' failed under the small stack"; fail=1
  fi
}
# Harness self-check: a bogus subcommand exits with a usage error, which must not count as an overflow.
if overflowed no-such-subcommand; then
  echo "FAIL: harness self-check: a bogus subcommand was taken for a stack overflow"; fail=1
else
  echo "ok: harness self-check: bogus subcommand (exit $last_rc) is not taken for an overflow"
fi
expect_crash deep 13000
expect_crash control 20000
expect_pass scale 20000
expect_pass unit
expect_pass sim 1 40
expect_pass delbench 100000 fast

if [ $fail -eq 0 ]; then echo "ALL OK"; else echo "SOME CHECKS FAILED"; fi
exit $fail
