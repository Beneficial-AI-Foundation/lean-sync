#!/usr/bin/env bash
# Headless browser check: serve build/site, open the demo in each available browser for
# wasm32 and wasm64, and print the PASS/FAIL reports the page POSTs back (the server compares
# the output with the native build and checks numBits against the arch). Each browser/arch
# invocation gets a unique run id and must produce its own PASS; a crash, timeout or missing
# report counts as a failure. Requires a prior scripts/wasm/build.sh.
source "$(dirname "$0")/common.sh"
PORT="${PORT:-8765}"
TMP="$(mktemp -d)"
LOG="$TMP/serve.log"
node "$ROOT/wasm/serve.mjs" "$PORT" > "$LOG" 2>&1 &
SERVER=$!
trap 'kill $SERVER 2>/dev/null; rm -rf "$TMP"' EXIT

deadline=$((SECONDS + 10))
until grep -q serving "$LOG"; do
  if ! kill -0 $SERVER 2>/dev/null || [ $SECONDS -ge $deadline ]; then
    echo "server failed to start on port $PORT:" >&2; cat "$LOG" >&2; exit 1
  fi
  sleep 0.2
done

RUNS=()   # "<run-id> <browser> <arch>"
for arch in wasm32 wasm64; do
  for browser in chromium firefox firefox-esr; do
    command -v $browser >/dev/null || continue
    run="$browser-$arch-$RANDOM$RANDOM"
    RUNS+=("$run $browser $arch")
    url="http://127.0.0.1:$PORT/index.html?arch=$arch&report=1&run=$run"
    mkdir -p "$TMP/profile-$run"
    # Browsers are killed by `timeout` after the page had time to report, so their exit
    # status carries no information; the per-run report below is what is checked.
    if [ $browser = chromium ]; then
      timeout 15 chromium --headless=new --no-sandbox --user-data-dir="$TMP/profile-$run" \
        --remote-debugging-port=0 "$url" >/dev/null 2>&1 || true
    else
      timeout 25 $browser --headless --no-remote --profile "$TMP/profile-$run" "$url" >/dev/null 2>&1 || true
    fi
  done
done

grep REPORT "$LOG" || true
fail=0
[ ${#RUNS[@]} -gt 0 ] || { echo "no browsers found" >&2; exit 1; }
for entry in "${RUNS[@]}"; do
  read -r run browser arch <<< "$entry"
  n_pass=$(grep -c "^REPORT PASS run=$run " "$LOG" || true)
  n_all=$(grep -c " run=$run " "$LOG" || true)
  if [ "$n_pass" -eq 1 ] && [ "$n_all" -eq 1 ]; then
    echo "OK   $browser $arch"
  else
    echo "FAIL $browser $arch (reports: $n_all, passes: $n_pass)"; fail=1
  fi
done
exit $fail
