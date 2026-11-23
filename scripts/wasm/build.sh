#!/usr/bin/env bash
# One-command build of the Lean -> wasm spike.
#   scripts/wasm/build.sh            # both wasm32 and wasm64
#   scripts/wasm/build.sh wasm32     # just one
# Produces build/site/ (static page: index.html, host.mjs, wasm32/, wasm64/).
source "$(dirname "$0")/common.sh"
ARCHES=("${@:-wasm32}")
[ $# -eq 0 ] && ARCHES=(wasm32 wasm64)

"$ROOT/scripts/wasm/fetch.sh"
cd "$ROOT" && lake build wasm-demo-native >/dev/null   # native reference for the Node check
"$ROOT/scripts/wasm/gen-c.sh" WasmDemo
for a in "${ARCHES[@]}"; do
  "$ROOT/scripts/wasm/build-runtime.sh" "$a"
  "$ROOT/scripts/wasm/build-wasm.sh" "$a"
done

SITE="$BUILD/site"
mkdir -p "$SITE"
cp "$ROOT/wasm/index.html" "$ROOT/wasm/host.mjs" "$SITE/"
for a in "${ARCHES[@]}"; do
  mkdir -p "$SITE/$a"
  cp "$BUILD/$a/lean_demo.mjs" "$BUILD/$a/lean_demo.wasm" "$SITE/$a/"
done
echo "site: $SITE  (serve with: python3 -m http.server -d $SITE 8000)"
