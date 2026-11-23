#!/usr/bin/env bash
# Build the libraries and run the native tests of the sync protocol and wire format
# (Tests/Sync.lean), including a small-stack run. Exit status is non-zero on any failure.
#
# Stack test, as in scripts/test-crdt.sh: compiled Lean runs `main` on a thread whose stack is
# LEAN_STACK_SIZE_KB (+128 KB runtime buffer). With STACK_KB (default 256) we require:
#   1. calibration: a trivial non-tail recursion of depth 13,000 (the spike's browser budget) crashes;
#   2. control: a deliberately non-tail-recursive encoding of the scale test's entries crashes,
#      so the scale test would catch per-entry recursion in the codec or the protocol;
#   3. unit, codec (fuzz included), a 40-seed simulation and the scale sync pass.
# Caveat: native and wasm frame sizes differ; the calibration is in frames of a trivial function.
set -uo pipefail
ulimit -c 0  # the expected overflows abort(); do not leave core dumps behind
cd "$(dirname "$0")/.."

STACK_KB=${STACK_KB:-256}
SCALE_N=${SCALE_N:-20000}
BIN=.lake/build/bin/sync-tests
fail=0

lake build || exit 1
lake build sync-tests || exit 1

# Forbidden constructs in the library. WARN only while the proofs are in progress.
if grep -rnE '\bsorry\b|^\s*axiom\b|native_decide|implemented_by|^\s*unsafe\b|^\s*partial\b' LeanSync LeanSync.lean; then
  echo "WARN: forbidden construct found in LeanSync/ (see above)"
else
  echo "ok: no sorry/axiom/native_decide/implemented_by/unsafe/partial in LeanSync/"
fi

echo "== full tests, default stack"
"$BIN" all || fail=1

echo "== stack test, LEAN_STACK_SIZE_KB=$STACK_KB"
# Succeed only if the run died the way a Lean stack overflow does: SIGABRT (exit status 134)
# and the runtime's "Stack overflow detected" diagnostic on stderr.
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
expect_crash control "$SCALE_N"
expect_pass unit
expect_pass codec
expect_pass sim 1 40
expect_pass scale "$SCALE_N"

if [ $fail -eq 0 ]; then echo "ALL OK"; else echo "SOME CHECKS FAILED"; fi
exit $fail
