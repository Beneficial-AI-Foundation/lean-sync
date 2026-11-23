#!/usr/bin/env bash
# All checks of the browser app (docs/app-design.md §10). Exit status non-zero on any failure.
#   scripts/test-app.sh            everything
#   E2E_ARGS="--only name" scripts/test-app.sh   pass options to test/e2e/run.mjs
# Steps: build the engine if needed and assemble build/site; regenerate the codec vectors and
# Lean's constructor lists from the current Lean build; Node unit tests (codec vs Lean, framing,
# blob streams, core with the real engine); the engine checks (scripts/wasm/check-engine.sh);
# the end-to-end scenarios in headless Chromium and Firefox (and Firefox ESR when installed).
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
fail=0
scripts/build-site.sh || exit 1
lake build sync-tests >/dev/null || exit 1
mkdir -p build/vectors
.lake/build/bin/sync-tests vectors build/vectors/codec.jsonl || exit 1
LEAN_PATH="$ROOT/.lake/build/lib/lean" lake env "${LEAN_TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0}/bin/lean" \
  --run scripts/wasm/Ctors.lean > build/vectors/ctors.json || exit 1
echo "== unit tests"
node --test test/unit/*.test.mjs || fail=1
echo "== engine checks"
scripts/wasm/check-engine.sh || fail=1
echo "== end-to-end"
node test/e2e/run.mjs ${E2E_ARGS:-} || fail=1
[ $fail -eq 0 ] && echo "APP CHECKS OK" || echo "APP CHECKS FAILED"
exit $fail
