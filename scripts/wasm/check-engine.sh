#!/usr/bin/env bash
# Checks of the wasm sync engine (needs a prior scripts/wasm/build.sh):
#   1. Node smoke test: initFresh + putMany through the real envelope (test/wasm-smoke.mjs);
#   2. native-vs-wasm replay of a simulator trace, byte for byte, plus a heap-growth bound
#      (test/wasm-replay.mjs; the trace comes from `sync-tests trace`);
#   3. a 20k-file sync between two wasm instances under Node (test/wasm-scale.mjs);
#   4. headless browsers (Chromium, Firefox, Firefox ESR when installed): test/browser-smoke.mjs.
# SEEDS (default 200) sets the number of simulator worlds replayed; SCALE_N (default 20000).
source "$(dirname "$0")/common.sh"
SEEDS="${SEEDS:-200}"; SCALE_N="${SCALE_N:-20000}"
cd "$ROOT"
lake build sync-tests >/dev/null
mkdir -p "$BUILD/vectors"
TRACE="$BUILD/vectors/sim-1-$SEEDS.bin"
.lake/build/bin/sync-tests trace 1 "$SEEDS" "$TRACE" | head -1
fail=0
node test/wasm-smoke.mjs || fail=1
node test/wasm-replay.mjs "$TRACE" || fail=1
node test/wasm-scale.mjs "$SCALE_N" || fail=1
node test/browser-smoke.mjs || fail=1
[ $fail -eq 0 ] && echo "ENGINE CHECKS OK" || echo "ENGINE CHECKS FAILED"
exit $fail
