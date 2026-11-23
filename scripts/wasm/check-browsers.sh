#!/usr/bin/env bash
# Headless browser check: serve build/site, open the demo in each available browser for
# wasm32 and wasm64, and print the PASS/FAIL reports the page POSTs back (the server compares
# the output with the native build). Requires a prior scripts/wasm/build.sh.
source "$(dirname "$0")/common.sh"
PORT="${PORT:-8765}"
TMP="$(mktemp -d)"
LOG="$TMP/serve.log"
node "$ROOT/wasm/serve.mjs" "$PORT" > "$LOG" 2>&1 &
SERVER=$!
trap 'kill $SERVER 2>/dev/null; rm -rf "$TMP"' EXIT
until grep -q serving "$LOG"; do sleep 0.2; done

for arch in wasm32 wasm64; do
  url="http://127.0.0.1:$PORT/index.html?arch=$arch&report=1"
  if command -v chromium >/dev/null; then
    timeout 15 chromium --headless=new --no-sandbox --user-data-dir="$TMP/chromium-$arch" \
      --remote-debugging-port=0 "$url" >/dev/null 2>&1 || true
  fi
  for ff in firefox firefox-esr; do
    command -v $ff >/dev/null || continue
    mkdir -p "$TMP/$ff-$arch"
    timeout 25 $ff --headless --no-remote --profile "$TMP/$ff-$arch" "$url" >/dev/null 2>&1 || true
  done
done
grep REPORT "$LOG" | sed -E 's/ platform="[^"]*"//'
! grep -q "REPORT FAIL" "$LOG"
