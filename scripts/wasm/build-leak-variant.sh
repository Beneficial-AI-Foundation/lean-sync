#!/usr/bin/env bash
# Test-only: link build/sync-leak/lean_sync.{mjs,wasm}, identical to the engine except that the
# shim leaks every input (-DLS_TEST_LEAK). Used as the negative control of the heap-growth check:
#   node test/wasm-replay.mjs --leak-only build/sync-leak/lean_sync.mjs   must FAIL.
# Needs a prior scripts/wasm/build.sh (reuses its closure list and objects).
source "$(dirname "$0")/common.sh"
T="$BUILD/sync-leak"; mkdir -p "$T"
cp "$BUILD/sync/modules.txt" "$T/modules.txt"
# build-wasm.sh compiles the shim itself; pass a wrapper source that defines the macro.
printf '#define LS_TEST_LEAK 1\n#include "%s"\n' "$ROOT/wasm/sync_shim.c" > "$T/leak_shim.c"
"$ROOT/scripts/wasm/build-wasm.sh" "$T" "$T/leak_shim.c" lean_sync createLeanSync \
  _ls_init,_ls_input,_ls_process,_ls_result,_ls_release
