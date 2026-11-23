#!/usr/bin/env bash
# Forbidden constructs in the libraries: `sorry`, `axiom`, `native_decide`, `implemented_by`,
# `unsafe`, `partial` as whole words anywhere outside comments and string literals (so
# `private partial def`, `@[inline] unsafe def` and `protected axiom` are caught, while a doc
# comment that says "partial" is not). Prints each hit as file:line: text; exit 1 on any hit.
# Usage: scripts/check-forbidden.sh DIR_OR_FILE...
set -uo pipefail
cd "$(dirname "$0")/.."
python3 - "$@" <<'PY'
import os, re, sys
charlit = re.compile(r"'(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")
words = re.compile(r'(?<![A-Za-z0-9_.\'])(sorry|axiom|native_decide|implemented_by|unsafe|partial)(?![A-Za-z0-9_\'])')

def strip(src):
    """Blank out comments (nested /- -/, --), character literals and string literals, keeping line
    structure. Character literals are handled before strings, so '"' does not open a string."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith('/-', i): depth += 1; out.append('  '); i += 2
            elif src.startswith('-/', i): depth -= 1; out.append('  '); i += 2
            else: out.append('\n' if c == '\n' else ' '); i += 1
        elif src.startswith('/-', i): depth = 1; out.append('  '); i += 2
        elif src.startswith('--', i):
            while i < n and src[i] != '\n': out.append(' '); i += 1
        elif c == "'" and (i == 0 or not (src[i-1].isalnum() or src[i-1] in "_'!?." or ord(src[i-1]) > 127)) \
                and charlit.match(src, i):
            # a character literal such as '"', '\'' or 'a' (a prime after an identifier is not one)
            m = charlit.match(src, i); out.append(' ' * (m.end() - i)); i = m.end()
        elif c == '"':
            out.append(' '); i += 1
            while i < n and src[i] != '"':
                if src[i] == '\\': out.append(' '); i += 1
                out.append('\n' if i < n and src[i] == '\n' else ' '); i += 1
            out.append(' '); i += 1
        else: out.append(c); i += 1
    return ''.join(out)

files = []
for a in sys.argv[1:]:
    if os.path.isdir(a):
        for root, _, fs in os.walk(a):
            files += [os.path.join(root, f) for f in fs if f.endswith('.lean')]
    elif a.endswith('.lean'):
        files.append(a)
hits = 0
for f in sorted(files):
    src = open(f, encoding='utf-8').read()
    orig = src.split('\n')
    for ln, line in enumerate(strip(src).split('\n'), 1):
        if words.search(line):
            print(f"{f}:{ln}: {orig[ln-1].strip()}"); hits += 1
sys.exit(1 if hits else 0)
PY
