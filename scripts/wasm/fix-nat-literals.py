#!/usr/bin/env python3
"""Make Lean-emitted C safe for wasm32 with respect to large Nat literals.

Problem (see docs/spike-lean-wasm.md): the Lean compiler types every Nat literal
< 2^32, and (on a 64-bit host) every literal <= 2^63-1, as `tagged`, i.e. an unboxed
scalar that needs no reference counting. On wasm32 a Nat is a scalar only below 2^31,
so `lean_unsigned_to_nat(N)` / `lean_cstr_to_nat("N")` for larger N return a heap
bignum with RC=1 that the emitted code never increments or decrements: it leaks
when used in borrowed positions and is freed twice when used in two owned positions.

Fix: replace each such literal with a per-call-site cached *persistent* object
(RC operations on persistent objects are no-ops). Nat objects are immutable, so
sharing is semantically invisible. Harmless (and a no-op in practice) on wasm64.

usage: fix-nat-literals.py SRC_DIR DST_DIR
Copies SRC_DIR/**.c to DST_DIR, rewriting files that need it, and only touching
destination files whose content changed (keeps incremental builds incremental).
"""
import os
import re
import sys

MACRO = r'''
/* wasm32 large-Nat-literal fix (scripts/wasm/fix-nat-literals.py) */
#define LEAN_WASM_LIT_NAT(s) ({ static lean_object* lean_wasm_lit_; \
  if (lean_wasm_lit_ == NULL) { lean_object* o_ = lean_cstr_to_nat(s); \
    if (!lean_is_scalar(o_)) lean_mark_persistent(o_); lean_wasm_lit_ = o_; } \
  lean_wasm_lit_; })
'''

CSTR = re.compile(r'lean_cstr_to_nat\("(\d+)"\)')
UNS = re.compile(r'lean_unsigned_to_nat\((\d+)u\)')


def fix(text):
    n = 0

    def cstr(m):
        nonlocal n
        n += 1
        return f'LEAN_WASM_LIT_NAT("{m.group(1)}")'

    def uns(m):
        nonlocal n
        v = int(m.group(1))
        if v < 2**31:
            return m.group(0)
        n += 1
        return f'LEAN_WASM_LIT_NAT("{v}")'

    out = CSTR.sub(cstr, text)
    out = UNS.sub(uns, out)
    if n:
        out = out.replace('#include <lean/lean.h>\n', '#include <lean/lean.h>\n' + MACRO, 1)
    return out, n


def main():
    src, dst = sys.argv[1], sys.argv[2]
    total_sites = total_files = 0
    for dirpath, _, files in os.walk(src):
        for f in files:
            if not f.endswith('.c'):
                continue
            s = os.path.join(dirpath, f)
            d = os.path.join(dst, os.path.relpath(s, src))
            with open(s) as fh:
                text, n = fix(fh.read())
            total_sites += n
            total_files += bool(n)
            old = None
            if os.path.exists(d):
                with open(d) as fh:
                    old = fh.read()
            if old != text:
                os.makedirs(os.path.dirname(d), exist_ok=True)
                with open(d, 'w') as fh:
                    fh.write(text)
    print(f'fix-nat-literals: rewrote {total_sites} literal sites in {total_files} files')


if __name__ == '__main__':
    main()
