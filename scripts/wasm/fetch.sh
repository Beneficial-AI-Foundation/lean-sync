#!/usr/bin/env bash
# Fetch the third-party sources needed to build the Lean runtime for wasm.
# Idempotent: skips checkouts that already exist.
source "$(dirname "$0")/common.sh"

mkdir -p "$VENDOR"
if [ ! -d "$VENDOR/lean4" ]; then
  git clone --depth 1 --branch "v$LEAN_VERSION" https://github.com/leanprover/lean4 "$VENDOR/lean4"
fi
got=$(git -C "$VENDOR/lean4" rev-parse HEAD)
[ "$got" = "$LEAN_GITHASH" ] || { echo "lean4 checkout is $got, expected $LEAN_GITHASH" >&2; exit 1; }
# Local fixes to upstream's (untested, commented-out-in-CI) Emscripten code paths.
# Each patch file starts with its upstream status (lean4#16089, PR #13298) and when it
# can be dropped. Lean is pinned at 4.36.0 for the demo.
for p in "$ROOT"/scripts/wasm/patches/lean4-*.patch; do
  if git -C "$VENDOR/lean4" apply --check "$p" 2>/dev/null; then
    git -C "$VENDOR/lean4" apply "$p"; echo "applied $(basename "$p")"
  fi
done

if [ ! -d "$LIBUV_SRC" ]; then
  # Only the headers are used (several runtime headers #include <uv.h> unconditionally);
  # the few libuv functions io.cpp still calls are stubbed in wasm/uv_stubs.c.
  git clone --depth 1 --branch "$LIBUV_TAG" https://github.com/libuv/libuv "$LIBUV_SRC"
fi

[ -x "$LEAN" ] || { echo "native Lean $LEAN_VERSION not found at $LEAN (install with elan)" >&2; exit 1; }
"$LEAN" --githash | grep -qx "$LEAN_GITHASH" || { echo "native lean githash mismatch" >&2; exit 1; }
command -v em++ >/dev/null || { echo "emscripten (em++) not on PATH" >&2; exit 1; }
echo "fetch: ok"
