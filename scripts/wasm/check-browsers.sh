#!/usr/bin/env bash
# Headless browser check: serve build/site and open the demo in each available browser,
# once with the default input and once per probe (`!panic`, `!deep 1000`). The page POSTs its
# result back; the server checks the module is 64-bit, compares the output byte for byte with
# the native build, and checks what the page displayed. Each invocation has a unique run id
# and must produce exactly one PASS; a crash, timeout or missing report counts as a failure.
# Requires a prior scripts/wasm/build.sh.
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

# name|URL-encoded ?input= value (empty: the page's default input)
CASES=("default|" "panic|%21panic" "deep1000|%21deep%201000")

RUNS=()   # "<run-id> <browser> <case>"
for browser in chromium firefox firefox-esr; do
  command -v $browser >/dev/null || continue
  for c in "${CASES[@]}"; do
    name="${c%%|*}"; input="${c#*|}"
    run="$browser-$name-$RANDOM$RANDOM"
    RUNS+=("$run $browser $name")
    url="http://127.0.0.1:$PORT/index.html?report=1&run=$run${input:+&input=$input}"
    mkdir -p "$TMP/profile-$run"
    if [ $browser = chromium ]; then
      timeout 30 chromium --headless=new --no-sandbox --user-data-dir="$TMP/profile-$run" \
        --remote-debugging-port=0 "$url" >/dev/null 2>&1 &
    else
      timeout 30 $browser --headless --no-remote --profile "$TMP/profile-$run" "$url" >/dev/null 2>&1 &
    fi
    pid=$!
    # Stop the browser as soon as its report arrives (or after 30 s). Its exit status carries
    # no information (it is always killed); the per-run report below is what is checked.
    until grep -q " run=$run " "$LOG" || ! kill -0 $pid 2>/dev/null; do sleep 0.2; done
    kill $pid 2>/dev/null || true; wait $pid 2>/dev/null || true
  done
done

grep REPORT "$LOG" || true
fail=0
[ ${#RUNS[@]} -gt 0 ] || { echo "no browsers found" >&2; exit 1; }
for entry in "${RUNS[@]}"; do
  read -r run browser name <<< "$entry"
  n_pass=$(grep -c "^REPORT PASS run=$run " "$LOG" || true)
  n_all=$(grep -c " run=$run " "$LOG" || true)
  if [ "$n_pass" -eq 1 ] && [ "$n_all" -eq 1 ]; then
    echo "OK   $browser $name"
  else
    echo "FAIL $browser $name (reports: $n_all, passes: $n_pass)"; fail=1
  fi
done
exit $fail
