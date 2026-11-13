#!/usr/bin/env bash
# The pinned caller of the mutex (examples/litmus-c/mutex). Adapted from examples/litmus-c/mutex/pin.sh.
#
#   examples/litmus-c/calls/pin.sh            # compile calls.c with the pinned gcc
#                                             # (examples/litmus-c/toolchains.txt) and flags
#                                             # plus -fno-optimize-sibling-calls, write
#                                             # obj/calls.o and objects.sha256, regenerate the
#                                             # Lean code module
#   examples/litmus-c/calls/pin.sh --check    # the object matches objects.sha256 and the Lean
#                                             # module matches the object (no compiler)
#   examples/litmus-c/calls/pin.sh --rebuild  # recompiling reproduces the pinned object
#
# The Lean module Silmaril/X86/Concurrency/Bridge/Crit/Code/Defs.lean holds the whole .text
# section of the object (the image: callers, callees and the padding between them) and the
# offset of each function symbol. The object must have no relocations (every call is
# `call rel32` inside .text). Untrusted tooling: the Lean side decodes the image itself and
# checks the call targets, the callees' `ret` bytes and every certificate by `decide`; this
# script only ties the bytes to the committed object.
set -euo pipefail
export LC_ALL=C
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
MODE=${1:-pin}
OUT=$ROOT/Silmaril/X86/Concurrency/Bridge/Crit/Code/Defs.lean
CC=/usr/bin/x86_64-linux-gnu-gcc-13
FLAGS=(-O2 -fcf-protection=none -fno-asynchronous-unwind-tables -g0 -fno-optimize-sibling-calls)
SRC=calls
# symbol  Lean-name
SYMS=(
  "mutex_lock lockOff"
  "mutex_unlock unlockOff"
  "crit_add2 critOff"
)

compile() { # dir
  "$CC" "${FLAGS[@]}" -c "$HERE/$SRC.c" -o "$1/$SRC.o"
}

gen() { # objdir > lean
  local tmp; tmp=$(mktemp -d)
  local o="$1/$SRC.o"
  if readelf -r "$o" | grep -q R_X86; then echo "relocations in $o" >&2; exit 1; fi
  objcopy -O binary -j .text "$o" "$tmp/text.bin"
  local size; size=$(stat -c %s "$tmp/text.bin")
  cat <<'HDR'
module

public import Silmaril.X86.Litmus.Extract.Defs

/-!
# The pinned image of the mutex caller

**Generated** by `examples/litmus-c/calls/pin.sh` from the pinned object
`examples/litmus-c/calls/obj/calls.o` (gcc 13.3.0, `-O2 -fcf-protection=none
-fno-asynchronous-unwind-tables -g0 -fno-optimize-sibling-calls`; `objects.sha256`): the whole
`.text` section and the offset of each function symbol. `pin.sh --check` regenerates this file
from the object and compares it byte for byte. Do not edit.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Bridge.Crit.Code

/-- Bytes from a list of naturals. -/
def bs (l : List Nat) : List (BitVec 8) := l.map (BitVec.ofNat 8)
HDR
  local bytes
  bytes=$(od -An -tx1 -v "$tmp/text.bin" | tr -s ' \n' ' ' |
    sed 's/^ //; s/ $//; s/\([0-9a-f][0-9a-f]\)/0x\1,/g; s/,$//')
  printf '\n/-- The `.text` section of `%s.o` (%d bytes). -/\n' "$SRC" "$size"
  printf 'def image : List (BitVec 8) := bs\n  [%s]\n' "$(echo "$bytes" | fold -s -w 90 | sed 's/ *$//; 2,$s/^/   /')"
  for row in "${SYMS[@]}"; do
    read -r sym lean <<<"$row"
    local off
    off=$(nm "$o" | awk -v f="$sym" '$3 == f { print $1 }')
    [ -n "$off" ] || { echo "no symbol $sym" >&2; exit 1; }
    printf '\n/-- The offset of `%s` in the image. -/\n' "$sym"
    printf 'def %s : Nat := 0x%x\n' "$lean" $((16#$off))
  done
  printf '\nend Silmaril.X86.Concurrency.Bridge.Crit.Code\n'
  rm -rf "$tmp"
}

case "$MODE" in
  pin)
    compile "$HERE/obj"
    (cd "$HERE/obj" && sha256sum ./*.o) > "$HERE/objects.sha256"
    mkdir -p "$(dirname "$OUT")"
    gen "$HERE/obj" > "$OUT"
    echo "pinned $SRC.o; wrote $OUT"
    ;;
  --check)
    (cd "$HERE/obj" && sha256sum -c --quiet "$HERE/objects.sha256")
    diff -u "$OUT" <(gen "$HERE/obj")
    echo "objects and $OUT are up to date"
    ;;
  --rebuild)
    tmp=$(mktemp -d)
    compile "$tmp"
    cmp "$tmp/$SRC.o" "$HERE/obj/$SRC.o"
    rm -rf "$tmp"
    echo "recompiling reproduces the pinned object"
    ;;
  *) echo "usage: $0 [--check|--rebuild]" >&2; exit 2 ;;
esac
