#!/usr/bin/env bash
# Compile the generated C of one closure plus a shim, and link <outdir>/<name>.{mjs,wasm}.
# usage: build-wasm.sh <outdir> <shim.c> <name> <ExportName> <exported functions, comma-separated>
# Only the modules listed in <outdir>/modules.txt (written by gen-c.sh) are linked, so several
# targets can share the build/c and build/obj caches.
source "$(dirname "$0")/common.sh"
TDIR="${1:?outdir}"; SHIM="${2:?shim}"; NAME="${3:?name}"; EXPORT_NAME="${4:?export name}"; FUNCS="${5:?exports}"
OBJ="$BUILD/obj"
mkdir -p "$OBJ"

CFLAGS="$(common_cflags) -Wno-unused-parameter -Wno-unused-label -Wno-unused-but-set-variable"
export CFLAGS OBJ BUILD
sed 's|\.|/|g' "$TDIR/modules.txt" | xargs -P "$JOBS" -I{} bash -c '
  src="$BUILD/c/{}.c"; o="$OBJ/{}.o"
  if [ ! -f "$o" ] || [ "$src" -nt "$o" ]; then
    mkdir -p "$(dirname "$o")"
    emcc $CFLAGS -c "$src" -o "$o" 2>"$o.err" || { cat "$o.err" >&2; exit 255; }
  fi'
emcc $CFLAGS -c "$SHIM" -o "$TDIR/shim.o"

# -sSTACK_SIZE: Emscripten's default (64 KiB) is far too small for Lean's non-tail recursion.
# -sMODULARIZE/EXPORT_ES6: one ES module usable from both the browser and Node.
LDFLAGS=(
  -O2 -fwasm-exceptions $WASM_ARCH_FLAGS ${LINK_EXTRA:-}
  -sALLOW_MEMORY_GROWTH=1 -sSTACK_SIZE=8MB
  -sMODULARIZE=1 -sEXPORT_ES6=1 -sEXPORT_NAME="$EXPORT_NAME"
  -sENVIRONMENT=web,node
  -sEXPORTED_FUNCTIONS="$FUNCS"
  -sEXPORTED_RUNTIME_METHODS=HEAPU8
)
mapfile -t OBJS < <(sed 's|\.|/|g; s|^|'"$OBJ"'/|; s|$|.o|' "$TDIR/modules.txt")
emcc "${LDFLAGS[@]}" "${OBJS[@]}" "$TDIR/shim.o" "$BUILD/libleanrt.a" -o "$TDIR/$NAME.mjs"
ls -l "$TDIR/$NAME.wasm" "$TDIR/$NAME.mjs"
