#!/usr/bin/env bash
# Compile the generated C (build/c) and the shim, and link build/lean_demo.{mjs,wasm}.
source "$(dirname "$0")/common.sh"
OBJ="$BUILD/obj"
mkdir -p "$OBJ"

CFLAGS="$(common_cflags) -Wno-unused-parameter -Wno-unused-label -Wno-unused-but-set-variable"
export CFLAGS OBJ BUILD
(cd "$BUILD/c" && find . -name '*.c' | sed 's|^\./||') | xargs -P "$JOBS" -I{} bash -c '
  src="$BUILD/c/{}"; o="$OBJ/{}"; o="${o%.c}.o"
  if [ ! -f "$o" ] || [ "$src" -nt "$o" ]; then
    mkdir -p "$(dirname "$o")"
    emcc $CFLAGS -c "$src" -o "$o" 2>"$o.err" || { cat "$o.err" >&2; exit 255; }
  fi'
emcc $CFLAGS -c "$ROOT/wasm/shim.c" -o "$OBJ/shim.o"

# -sSTACK_SIZE: Emscripten's default (64 KiB) is far too small for Lean's non-tail recursion.
# -sMODULARIZE/EXPORT_ES6: one ES module usable from both the browser and Node.
LDFLAGS=(
  -O2 -fwasm-exceptions $WASM_ARCH_FLAGS ${LINK_EXTRA:-}
  -sALLOW_MEMORY_GROWTH=1 -sSTACK_SIZE=8MB
  -sMODULARIZE=1 -sEXPORT_ES6=1 -sEXPORT_NAME=createLeanDemo
  -sENVIRONMENT=web,node
  -sEXPORTED_FUNCTIONS=_lw_init,_lw_input,_lw_process,_lw_result,_lw_release
  -sEXPORTED_RUNTIME_METHODS=HEAPU8
)
mapfile -t OBJS < <(find "$OBJ" -name '*.o' | sort)
emcc "${LDFLAGS[@]}" "${OBJS[@]}" "$BUILD/libleanrt.a" -o "$BUILD/lean_demo.mjs"
ls -l "$BUILD/lean_demo.wasm" "$BUILD/lean_demo.mjs"
