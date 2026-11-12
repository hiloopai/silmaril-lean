#!/usr/bin/env bash
# The pinned executables of the dynamic-linking proofs (examples/dyn/pins.txt).
#   pin.sh --check        the committed files in pinned/ have the sha256 of pins.txt (default)
#   pin.sh --build [NAME] rebuild from the C sources in a scratch directory (from the source's
#                         basename, so the bytes do not depend on the checkout path) with $GCC
#                         (default gcc) or $CLANG (default clang-18), compare with pins.txt and,
#                         if equal, write pinned/NAME. Needs the toolchain named in pins.txt.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
pins="$here/pins.txt"
mode=${1:---check}; shift || true
GCC=${GCC:-gcc}; CLANG=${CLANG:-clang-18}
GCC_DIR=${GCC_DIR:-/usr/lib/gcc/x86_64-linux-gnu/13}  # clang links GCC 13's crt objects
names=("$@")
[ ${#names[@]} -gt 0 ] || mapfile -t names < <(awk '!/^#/ && NF {print $1}' "$pins")
fail=0
for name in "${names[@]}"; do
  read -r _ want _ cc src < <(awk -v n="$name" '$1==n' "$pins") || { echo "pin.sh: unknown pin $name" >&2; exit 2; }
  case "$mode" in
    --check)
      got=$(sha256sum "$here/pinned/$name" | cut -d' ' -f1)
      if [ "$got" = "$want" ]; then echo "ok $name"; else echo "pin.sh: $name: sha256 $got, pins.txt wants $want" >&2; fail=1; fi ;;
    --build)
      tmp=$(mktemp -d); cp "$here/$src" "$tmp/"
      case "$cc" in gcc) c=("$GCC") ;; clang) c=("$CLANG" --gcc-install-dir="$GCC_DIR") ;; esac
      (cd "$tmp" && "${c[@]}" -O2 -o out "$(basename "$src")")
      got=$(sha256sum "$tmp/out" | cut -d' ' -f1)
      if [ "$got" = "$want" ]; then cp "$tmp/out" "$here/pinned/$name"; echo "wrote $name"
      else echo "pin.sh: $name: built sha256 $got, pins.txt wants $want (toolchain differs?)" >&2; fail=1; fi
      rm -rf "$tmp" ;;
    *) echo "usage: pin.sh [--check|--build] [NAME...]" >&2; exit 2 ;;
  esac
done
exit $fail
