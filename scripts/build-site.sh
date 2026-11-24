#!/usr/bin/env bash
# Assemble the static site in build/site/: the app (app/) plus the wasm engine (build/sync/).
# Builds the engine first if it is missing (scripts/wasm/build.sh). Any static host can serve
# build/site/; the dev server (node dev/serve.mjs) also provides the test transport.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
[ -f "$ROOT/build/sync/lean_sync.wasm" ] || "$ROOT/scripts/wasm/build.sh"
SITE="$ROOT/build/site"
rm -rf "$SITE"; mkdir -p "$SITE/lean"
cp -r "$ROOT/app/." "$SITE/"
cp "$ROOT/build/sync/lean_sync.mjs" "$ROOT/build/sync/lean_sync.wasm" "$SITE/lean/"
echo "site: $SITE ($(du -sh "$SITE" | cut -f1)); serve with: node dev/serve.mjs --port 8000"
