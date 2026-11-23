# Shared settings for the Lean -> wasm spike scripts. Sourced, not executed.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LEAN_VERSION="4.36.0"
LEAN_GITHASH="611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"
LIBUV_TAG="v1.48.0"   # the version lean4's CMakeLists.txt pins for Emscripten

VENDOR="$ROOT/vendor"
LEAN_SRC="$VENDOR/lean4/src"
LIBUV_SRC="$VENDOR/libuv"
BUILD="$ROOT/build"

# The native toolchain is used only to *generate C* (and must be the same version).
LEAN_TC="${LEAN_TC:-$HOME/.elan/toolchains/leanprover--lean4---v${LEAN_VERSION}}"
LEAN="$LEAN_TC/bin/lean"

JOBS="${JOBS:-$(nproc)}"

# Per-architecture flags. ARCH is wasm32 or wasm64.
arch_flags() {
  case "$1" in
    wasm32) echo "" ;;
    wasm64) echo "-m64" ;;   # = Emscripten MEMORY64 (the -s spelling is deprecated)
    *) echo "unknown arch $1" >&2; exit 1 ;;
  esac
}

# Flags shared by every C/C++ compilation unit (runtime and Lean-emitted C).
#  - LEAN_EMSCRIPTEN: upstream's switch that stubs out libuv/openssl/threads-specific code
#  - no LEAN_MULTI_THREAD, no LEAN_USE_GMP (Lean's own mpn bignums), no LEAN_MMAP,
#    no mimalloc (Emscripten's dlmalloc is used)
#  - -fwasm-exceptions: the runtime uses C++ exceptions (lean::throwable) internally
common_cflags() {
  echo "-O2 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions $(arch_flags "$1") \
    -I$BUILD/gen/include -I$LEAN_SRC/include -I$LEAN_SRC -I$LIBUV_SRC/include"
}
