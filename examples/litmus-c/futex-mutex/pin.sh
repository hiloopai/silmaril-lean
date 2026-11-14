#!/usr/bin/env bash
# The pinned futex mutex. Adapted from examples/litmus-c/mutex/pin.sh.
#
#   examples/litmus-c/futex-mutex/pin.sh            # compile fmutex.c with the pinned gcc
#                                             # (examples/litmus-c/toolchains.txt), write
#                                             # obj/fmutex.o and objects.sha256, regenerate the
#                                             # Lean code module
#   examples/litmus-c/futex-mutex/pin.sh --check    # the object matches objects.sha256 and the Lean
#                                             # module matches the object (no compiler)
#   examples/litmus-c/futex-mutex/pin.sh --rebuild  # recompiling reproduces the pinned object
#
# The Lean module Silmaril/X86/Concurrency/Cir/Mutex/Futex/Code/Defs.lean holds, for each function, its
# bytes from its symbol up to (not including) its final `ret`; the script checks that the byte
# there is C3 and that the object has no relocations. Untrusted tooling: the Lean side checks the
# bytes it is given (the translation-validation certificates are checked against them by
# `decide`), and this script only ties them to the committed objects.
set -euo pipefail
export LC_ALL=C
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
MODE=${1:-pin}
OUT=$ROOT/Silmaril/X86/Concurrency/Cir/Mutex/Futex/Code/Defs.lean
CC=/usr/bin/x86_64-linux-gnu-gcc-13
FLAGS=(-O2 -fcf-protection=none -fno-asynchronous-unwind-tables -g0)
SRCS=(fmutex)
# function  object  Lean-name
FNS=(
  "fmutex_lock fmutex fmutexLock"
  "fmutex_unlock fmutex fmutexUnlock"
  "fmutex_unlock_dec fmutex fmutexUnlockDec"
)

compile() { # dir
  for s in "${SRCS[@]}"; do "$CC" "${FLAGS[@]}" -c "$HERE/$s.c" -o "$1/$s.o"; done
}

gen() { # objdir > lean
  local tmp; tmp=$(mktemp -d)
  cat <<'EOF'
module

public import Silmaril.X86.Litmus.Extract.Defs

/-!
# The pinned code of the futex mutex

**Generated** by `examples/litmus-c/futex-mutex/pin.sh` from the pinned objects
`examples/litmus-c/futex-mutex/obj/*.o` (gcc 13.3.0, `-O2 -fcf-protection=none
-fno-asynchronous-unwind-tables -g0`; `objects.sha256`). Each list is one function's bytes
from its symbol up to, not including, its final `ret` (`C3`). `pin.sh --check` regenerates
this file from the objects and compares it byte for byte. Do not edit.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Mutex.Futex.Code

/-- Bytes from a list of naturals. -/
def bs (l : List Nat) : List (BitVec 8) := l.map (BitVec.ofNat 8)
EOF
  for row in "${FNS[@]}"; do
    read -r fn obj lean <<<"$row"
    local o="$1/$obj.o"
    if readelf -r "$o" | grep -q R_X86; then echo "relocations in $o" >&2; exit 1; fi
    objcopy -O binary -j .text "$o" "$tmp/$obj.bin"
    local start next
    start=$((16#$(nm "$o" | awk -v f="$fn" '$3 == f { print $1 }')))
    # the function's end: the next symbol, or the end of .text
    next=$(nm -n "$o" | awk -v s="$start" '$2 == "T" { v = strtonum("0x" $1); if (v > s) { print v; exit } }')
    [ -n "$next" ] || next=$(stat -c %s "$tmp/$obj.bin")
    # the last `ret` (C3) before the function's end, found by disassembly
    local ret
    ret=$(objdump -d --no-show-raw-insn "$o" | awk -v s="$start" -v e="$next" '
      /^ *[0-9a-f]+:/ { a = strtonum("0x" substr($1, 1, length($1) - 1));
                        if (a >= s && a < e && $2 == "ret") r = a }
      END { print r }')
    [ -n "$ret" ] || { echo "no ret in $fn" >&2; exit 1; }
    local b
    b=$(od -An -tx1 -v -j "$ret" -N 1 "$tmp/$obj.bin" | tr -d ' ')
    [ "$b" = c3 ] || { echo "byte at ret of $fn is $b" >&2; exit 1; }
    local bytes
    bytes=$(od -An -tx1 -v -j "$start" -N $((ret - start)) "$tmp/$obj.bin" | tr -s ' \n' ' ' |
      sed 's/^ //; s/ $//; s/\([0-9a-f][0-9a-f]\)/0x\1,/g; s/,$//')
    printf '\n/-- `%s` (`%s.o`, %d bytes before its `ret`). -/\n' "$fn" "$obj" $((ret - start))
    printf 'def %s : List (BitVec 8) := bs\n  [%s]\n' "$lean" "$(echo "$bytes" | fold -s -w 90 | sed 's/ *$//; 2,$s/^/   /')"
  done
  printf '\nend Silmaril.X86.Concurrency.Cir.Mutex.Futex.Code\n'
  rm -rf "$tmp"
}

case "$MODE" in
  pin)
    compile "$HERE/obj"
    (cd "$HERE/obj" && sha256sum ./*.o) > "$HERE/objects.sha256"
    gen "$HERE/obj" > "$OUT"
    echo "pinned ${#SRCS[@]} objects; wrote $OUT"
    ;;
  --check)
    (cd "$HERE/obj" && sha256sum -c --quiet "$HERE/objects.sha256")
    diff -u "$OUT" <(gen "$HERE/obj")
    echo "objects and $OUT are up to date"
    ;;
  --rebuild)
    tmp=$(mktemp -d)
    compile "$tmp"
    for s in "${SRCS[@]}"; do cmp "$tmp/$s.o" "$HERE/obj/$s.o"; done
    rm -rf "$tmp"
    echo "recompiling reproduces the pinned objects"
    ;;
  *) echo "usage: $0 [--check|--rebuild]" >&2; exit 2 ;;
esac
