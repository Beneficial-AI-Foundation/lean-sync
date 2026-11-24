#!/usr/bin/env bash
# One-command build of the sync engine (LeanSync.Envelope) for wasm64.
#   scripts/wasm/build.sh
# Produces build/sync/lean_sync.{mjs,wasm}: an ES module exporting `createLeanSync`, whose
# instance exposes _ls_init/_ls_input/_ls_process/_ls_result/_ls_release (wasm/sync_shim.c).
source "$(dirname "$0")/common.sh"
TDIR="$BUILD/sync"
t0=$SECONDS
"$ROOT/scripts/wasm/fetch.sh"
t1=$SECONDS
"$ROOT/scripts/wasm/gen-c.sh" LeanSync.Envelope "$TDIR"
t2=$SECONDS
"$ROOT/scripts/wasm/build-runtime.sh"
t3=$SECONDS
"$ROOT/scripts/wasm/build-wasm.sh" "$TDIR" "$ROOT/wasm/sync_shim.c" lean_sync createLeanSync \
  _ls_init,_ls_input,_ls_process,_ls_result,_ls_release
t4=$SECONDS
echo "timings (s): fetch $((t1-t0)), gen-c $((t2-t1)), runtime $((t3-t2)), compile+link $((t4-t3)), total $((t4-t0))"
