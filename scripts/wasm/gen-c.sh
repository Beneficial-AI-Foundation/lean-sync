#!/usr/bin/env bash
# Generate C for every module in the import closure of the demo, using the native Lean
# toolchain of the same version:
#   - our own modules come from Lake (`lake build`, C lands in .lake/build/ir)
#   - Init/Std modules are re-elaborated from the matching lean4 sources with `lean -c`
#     (the release ships oleans and static libs for them, but not their C).
# Output: build/c/<Module/Path>.c and build/c/modules.txt
source "$(dirname "$0")/common.sh"
ROOT_MODULE="${1:-WasmDemo}"
OUT="$BUILD/c"
mkdir -p "$OUT"

cd "$ROOT"
lake build "$ROOT_MODULE" >/dev/null
LEAN_PATH="$ROOT/.lake/build/lib/lean" lake env "$LEAN" --run scripts/wasm/ModClosure.lean "$ROOT_MODULE" > "$OUT/modules.txt"

export LEAN LEAN_SRC OUT ROOT
grep -E '^(Init|Std|Lean)(\.|$)' "$OUT/modules.txt" | xargs -P "$JOBS" -I{} bash -c '
  m={}; rel="${m//.//}"; src="$LEAN_SRC/$rel.lean"; dst="$OUT/$rel.c"
  if [ ! -f "$dst" ] || [ "$src" -nt "$dst" ]; then
    mkdir -p "$(dirname "$dst")"
    # Linters have no effect on generated code; turning them off just saves time.
    (cd "$LEAN_SRC" && "$LEAN" --root=. -Dlinter.all=false -c "$dst.tmp" "$rel.lean" >/dev/null) \
      && mv "$dst.tmp" "$dst" || { echo "C generation failed for $m" >&2; exit 255; }
  fi'

# Our own modules: Lake already produced the C.
grep -vE '^(Init|Std|Lean)(\.|$)' "$OUT/modules.txt" | while read -r m; do
  rel="${m//.//}"; mkdir -p "$(dirname "$OUT/$rel.c")"
  cp "$ROOT/.lake/build/ir/$rel.c" "$OUT/$rel.c"
done
echo "gen-c: $(wc -l < "$OUT/modules.txt") modules -> $OUT"
