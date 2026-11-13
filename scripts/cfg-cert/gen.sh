#!/usr/bin/env bash
# Regenerate the effects examples' certificates (Silmaril/Elf/Effects/Example/*/Defs.lean).
#   scripts/cfg-cert/gen.sh LIBC TRUE SHA256SUM [--check]
# LIBC: Ubuntu libc6 2.39-0ubuntu8.9 libc.so.6 (sha256 3a15d668...98bf);
# TRUE, SHA256SUM: /usr/bin/true, /usr/bin/sha256sum of Ubuntu coreutils 9.4-3ubuntu6.3
# (sha256 8a63c983...ae28, 4d2db56c...9a60). With --check, fail if a module differs.
set -euo pipefail
cd "$(dirname "$0")/../.."
libc=$1 true_=$2 sha=$3 check=${4:-}
want() { [ "$(sha256sum "$1" | cut -d' ' -f1)" = "$2" ] || { echo "gen.sh: $1: unexpected sha256" >&2; exit 1; }; }
want "$libc" 3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf
want "$true_" 8a63c98320173f79e263115e10cefc170155e47d1fd4b5a70e4429d2699cae28
want "$sha" 4d2db56c867e5324e0084c9e897f6360d37517de77ac96f2bd31494223d69a60
cargo build --quiet --release --manifest-path tools/cfg-cert/Cargo.toml
gen=tools/cfg-cert/target/release/cfg-cert
ex=Silmaril/Elf/Effects/Example
emit() {  # emit NAME ARGS...
  local name=$1; shift
  local out=$ex/$name/Defs.lean tmp
  tmp=$(mktemp)
  "$gen" "$@" --module "Silmaril.Elf.Effects.Example.$name" > "$tmp"
  if [ "$check" = --check ]; then cmp -s "$tmp" "$out" || { echo "gen.sh: $out differs" >&2; rm -f "$tmp"; exit 1; }; rm -f "$tmp"
  else mkdir -p "$ex/$name"; mv "$tmp" "$out"; fi
}
emit Strlen --elf "$libc" --entry 0xb4dc0 --entry 0xc1a10 --entry 0x194580 --entry 0x18bac0 --entry 0x19bc40 \
  --title "glibc 2.39 (Ubuntu 2.39-0ubuntu8.9) strlen: the IFUNC resolver and its four implementations" \
  --license "machine code of the GNU C Library, LGPL-2.1-or-later"
emit CoreutilsTrue --elf "$true_" --entry 0x1490 \
  --title 'GNU coreutils 9.4 (Ubuntu 9.4-3ubuntu6.3) `true`, from `main`' \
  --license "machine code of GNU coreutils, GPL-3.0-or-later"
emit Sha256sum --elf "$sha" --entry 0x2750 \
  --title 'GNU coreutils 9.4 (Ubuntu 9.4-3ubuntu6.3) `sha256sum`, from `main`' \
  --license "machine code of GNU coreutils, GPL-3.0-or-later"
