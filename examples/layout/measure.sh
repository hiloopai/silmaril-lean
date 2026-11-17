#!/usr/bin/env bash
# Measure the cases of cases.h with real compilers (examples/layout/README.md):
#   gcc (x86-64 System V): sizeof, _Alignof, and every member's bit offset and width, found at run
#     time (a bit-field set to all ones in a zeroed object; an ordinary member by offsetof/sizeof);
#   clang --target=x86_64-pc-windows-msvc (Microsoft x64): -Xclang -fdump-record-layouts.
# Output: gcc-x86_64.txt and msvc-x64.txt, lines `CASE size align` then `  MEMBER bitoff width`.
#   examples/layout/measure.sh            (in the image built from examples/layout/Dockerfile)
set -euo pipefail
cd "$(dirname "$0")"
cases=$(grep -oE '^(struct|union) [a-z0-9]+' cases.h)
probe=$(mktemp -d)/probe.c
{
  echo '#include <stdio.h>'; echo '#include <stddef.h>'; echo '#include <string.h>'; echo '#include "cases.h"'
  echo 'static int lo(const unsigned char *p, size_t n){for(size_t i=0;i<8*n;i++) if(p[i/8]>>(i%8)&1) return (int)i; return -1;}'
  echo 'static int hi(const unsigned char *p, size_t n){int h=-1;for(size_t i=0;i<8*n;i++) if(p[i/8]>>(i%8)&1) h=(int)i; return h;}'
  echo 'int main(void){'
  while read -r kind tag; do
    echo "  { $kind $tag x; printf(\"$tag %zu %zu\\n\", sizeof x, _Alignof($kind $tag));"
    # members: parse `type name : w;` or `type name;` from the case line (cases are one line each)
    line=$(grep -E "^$kind $tag " cases.h)
    body=${line#*\{}; body=${body%\}*}
    IFS=';' read -ra decls <<< "$body"
    for d in "${decls[@]}"; do
      d=$(echo "$d" | sed 's/^ *//; s/ *$//'); [ -z "$d" ] && continue
      if [[ "$d" == *:* ]]; then
        name=$(echo "${d%%:*}" | awk '{print $NF}'); w=$(echo "${d##*:}" | tr -d ' ')
        if [[ "$name" == "int" || "$name" == "char" || "$name" == "short" || "$name" == "long" ]]; then name=""; fi
        if [ -z "$name" ]; then echo "    printf(\"  - ? $w\\n\");"; continue; fi
        echo "    memset(&x,0,sizeof x); x.$name = ~0; printf(\"  $name %d %d\\n\", lo((unsigned char*)&x,sizeof x), hi((unsigned char*)&x,sizeof x)-lo((unsigned char*)&x,sizeof x)+1);"
      else
        name=$(echo "$d" | sed 's/\[.*//' | awk '{print $NF}' | tr -d '*')
        echo "    printf(\"  $name %zu %zu\\n\", 8*offsetof($kind $tag, $name), 8*sizeof x.$name);"
      fi
    done
    echo "  }"
  done <<< "$cases"
  echo 'return 0;}'
} > "$probe"
cp cases.h "$(dirname "$probe")/"
gcc -std=gnu11 -O0 -w "$probe" -o "${probe%.c}" && "${probe%.c}" > gcc-x86_64.txt
{ echo "# $(gcc --version | head -1)"; cat gcc-x86_64.txt; } > gcc.tmp && mv gcc.tmp gcc-x86_64.txt
# Microsoft x64: clang's MSVC-compatible record layout
cat cases.h > "$probe.ms.c"
while read -r kind tag; do echo "int sz_$tag = sizeof($kind $tag);" >> "$probe.ms.c"; done <<< "$cases"
clang-18 --target=x86_64-pc-windows-msvc -fsyntax-only -Xclang -fdump-record-layouts -w "$probe.ms.c" > dump.txt
python3 -I - dump.txt > msvc-x64.txt <<'PY'
import re, sys
out, cur = [], None
for line in open(sys.argv[1]):
    m = re.match(r'\s*0 \| (struct|union) (\w+)$', line)
    if m: cur, members = m.group(2), []; continue
    if cur is None: continue
    m = re.match(r'\s*\|\s*\[sizeof=(\d+), align=(\d+)', line)
    if m:
        out.append(f"{cur} {m.group(1)} {m.group(2)}")
        out.extend(f"  {n} {o} {w}" for (n, o, w) in members)
        cur = None
        continue
    m = re.match(r'\s*(\d+)(?::(\d+)-(\d+))? \|\s+(\S.*)$', line)
    if m:
        off, b0, b1, decl = m.groups()
        words = decl.replace('*', ' ').split()
        if b0 is not None:   # a bit-field: its bit range
            name = words[-1] if len(words) > 1 and words[-1] not in ('int', 'char', 'short', 'long', 'unsigned') else '-'
            members.append((name, 8 * int(off) + int(b0), int(b1) - int(b0) + 1))
        else:                # an ordinary member: its offset (the width is not in the dump)
            members.append((words[-1].split('[')[0], 8 * int(off), '?'))
print("# clang (MSVC record layout, --target=x86_64-pc-windows-msvc)")
print("\n".join(out))
PY
rm -f dump.txt
