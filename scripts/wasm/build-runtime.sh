#!/usr/bin/env bash
# Build the Lean C++ runtime (src/runtime) with Emscripten into build/libleanrt.a.
source "$(dirname "$0")/common.sh"
OUT="$BUILD/rt"
mkdir -p "$OUT" "$BUILD/gen/include/lean"

# Headers normally produced by CMake's configure_file.
G="$BUILD/gen/include"
cat > "$G/lean/config.h" <<EOF
#pragma once
#include <lean/version.h>
#define LEAN_IS_STAGE0 0
EOF
cat > "$G/lean/version.h" <<EOF
#pragma once
#define LEAN_VERSION_MAJOR 4
#define LEAN_VERSION_MINOR 36
#define LEAN_VERSION_PATCH 0
#define LEAN_VERSION_IS_RELEASE 1
#define LEAN_SPECIAL_VERSION_DESC ""
#define LEAN_VERSION_STRING "$LEAN_VERSION"
#define LEAN_PLATFORM_TARGET "wasm-unknown-emscripten"
#define LEAN_MANUAL_ROOT ""
EOF
echo "#define LEAN_GITHASH \"$LEAN_GITHASH\"" > "$G/githash.h"

# Same file list as src/runtime/CMakeLists.txt, minus mimalloc. cadical.cpp is built without
# LEAN_CADICAL, i.e. as the stub upstream uses when the SAT solver is not linked.
SRCS=(debug thread mpz utf8 object apply exception interrupt memory stackinfo compact
      init_module io hash byteslice platform alloc allocprof sharecommon stack_overflow
      process object_ref mpn mutex libuv openssl cadical
      uv/net_addr uv/event_loop uv/timer uv/tcp uv/udp uv/dns uv/system uv/signal)

CFLAGS="$(common_cflags) -std=c++20 -Wno-deprecated-declarations"
export CFLAGS OUT LEAN_SRC
printf '%s\n' "${SRCS[@]}" | xargs -P "$JOBS" -I{} bash -c '
  f={}; o="$OUT/${f//\//_}.o"
  if [ ! -f "$o" ] || [ "$LEAN_SRC/runtime/$f.cpp" -nt "$o" ]; then
    em++ $CFLAGS -c "$LEAN_SRC/runtime/$f.cpp" -o "$o" || exit 255
  fi'
emcc $(common_cflags) -c "$ROOT/wasm/uv_stubs.c" -o "$OUT/uv_stubs.o"
rm -f "$BUILD/libleanrt.a"
emar rcs "$BUILD/libleanrt.a" "$OUT"/*.o
echo "runtime: $BUILD/libleanrt.a"
