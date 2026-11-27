#!/usr/bin/env bash
# Checks of the browser app (docs/app-design.md §10). Exit status non-zero on any failure.
#   scripts/test-app.sh            quick smoke set (about 2 minutes)
#   scripts/test-app.sh --full     everything: all engine checks and every e2e scenario and browser pair
#   E2E_ARGS="--only name" scripts/test-app.sh   pass options to test/e2e/run.mjs
# Steps: build the engine if needed and assemble build/site; regenerate the codec vectors and
# Lean's constructor lists from the current Lean build; Node unit tests (codec vs Lean, framing,
# blob streams, core with the real engine); quick: a Node smoke of the wasm engine and the e2e
# smoke set (one browser combination per scenario); --full: scripts/wasm/check-engine.sh (replay,
# leak, scale, browser smoke) and every e2e scenario (`run.mjs --all`).
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
fail=0
full=0; [ "${1:-}" = "--full" ] && full=1
# One directory for every temporary browser profile of this run (honours TMPDIR); every process
# whose command line mentions it is ours. Both are checked at the end, separately from the results.
export LEANSYNC_TEST_DIR="$(mktemp -d "${TMPDIR:-/tmp}/leansync-app-XXXXXX")"
ours() { pgrep -f -- "$LEANSYNC_TEST_DIR" || true; }
cleanup() { local p; p=$(ours); [ -n "$p" ] && kill -9 $p 2>/dev/null; rm -rf "$LEANSYNC_TEST_DIR" 2>/dev/null || true; }
trap 'cleanup; exit 130' INT TERM
scripts/build-site.sh || exit 1
lake build sync-tests >/dev/null || exit 1
mkdir -p build/vectors
.lake/build/bin/sync-tests vectors build/vectors/codec.jsonl || exit 1
LEAN_PATH="$ROOT/.lake/build/lib/lean" lake env "${LEAN_TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0}/bin/lean" \
  --run scripts/wasm/Ctors.lean > build/vectors/ctors.json || exit 1
echo "== unit tests"
node --test test/unit/*.test.mjs || fail=1
if [ $full -eq 1 ]; then
  echo "== engine checks"
  scripts/wasm/check-engine.sh || fail=1
  echo "== end-to-end (all)"
  node test/e2e/run.mjs --all ${E2E_ARGS:-} || fail=1
else
  echo "== engine smoke (Node)"
  node test/wasm-smoke.mjs || fail=1
  echo "== end-to-end (smoke set; --full for all)"
  node test/e2e/run.mjs ${E2E_ARGS:-} || fail=1
fi
echo "== hygiene"
left=$(ours)
clean=0
if [ -n "$left" ]; then echo "CLEANUP FAILED: processes still running:"; ps -o pid,args -p $(echo $left | tr ' ' ,) || true; clean=1; fi
rm -rf "$LEANSYNC_TEST_DIR" 2>/dev/null
for i in 1 2 3 4 5; do [ -e "$LEANSYNC_TEST_DIR" ] || break; sleep 1; rm -rf "$LEANSYNC_TEST_DIR" 2>/dev/null; done
if [ -e "$LEANSYNC_TEST_DIR" ]; then echo "CLEANUP FAILED: $LEANSYNC_TEST_DIR not removed"; clean=1; fi
[ $clean -eq 0 ] && echo "hygiene: no process left, $LEANSYNC_TEST_DIR removed"
cleanup
[ $fail -eq 0 ] && echo "APP CHECKS OK" || echo "APP CHECKS FAILED"
[ $clean -eq 0 ] || echo "(test results above are independent of the cleanup failure)"
[ $fail -eq 0 ] && [ $clean -eq 0 ]
