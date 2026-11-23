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

lake build || exit 1
lake build crdt-tests || exit 1

if grep -rnE '\bsorry\b|^\s*axiom\b|native_decide|implemented_by|^\s*unsafe\b' LeanCrdt LeanCrdt.lean; then
  echo "FAIL: forbidden construct found in LeanCrdt/"; fail=1
else
  echo "ok: no sorry/axiom/native_decide/implemented_by/unsafe in LeanCrdt/"
fi

echo "== full tests, default stack"
"$BIN" all || fail=1

echo "== stack test, LEAN_STACK_SIZE_KB=$STACK_KB"
expect_crash() {
  if LEAN_STACK_SIZE_KB=$STACK_KB "$BIN" "$@" >/dev/null 2>&1; then
    echo "FAIL: '$*' did not overflow: the stack limit is not tight enough to be meaningful"; fail=1
  else
    echo "ok: '$*' overflowed as expected"
  fi
}
expect_pass() {
  if LEAN_STACK_SIZE_KB=$STACK_KB "$BIN" "$@" > /dev/null; then
    echo "ok: '$*' passed under the small stack"
  else
    echo "FAIL: '$*' failed under the small stack"; fail=1
  fi
}
expect_crash deep 13000
expect_crash control 20000
expect_pass scale 20000
expect_pass unit
expect_pass sim 1 40

if [ $fail -eq 0 ]; then echo "ALL OK"; else echo "SOME CHECKS FAILED"; fi
exit $fail
