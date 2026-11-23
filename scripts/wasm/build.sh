#!/usr/bin/env bash
# One-command build of the Lean -> wasm64 spike.
#   scripts/wasm/build.sh
# Produces build/site/ (static page: index.html, host.mjs, lean_demo.{mjs,wasm}).
source "$(dirname "$0")/common.sh"

"$ROOT/scripts/wasm/fetch.sh"
cd "$ROOT" && lake build wasm-demo-native >/dev/null   # native reference for the checks
"$ROOT/scripts/wasm/gen-c.sh" WasmDemo
"$ROOT/scripts/wasm/build-runtime.sh"
"$ROOT/scripts/wasm/build-wasm.sh"

SITE="$BUILD/site"
mkdir -p "$SITE"
cp "$ROOT/wasm/index.html" "$ROOT/wasm/host.mjs" "$BUILD/lean_demo.mjs" "$BUILD/lean_demo.wasm" "$SITE/"
echo "site: $SITE  (serve with: node wasm/serve.mjs 8000)"
