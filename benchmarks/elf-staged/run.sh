#!/usr/bin/env bash
# Staged ELF parsing on a real multi-megabyte static executable (README.md beside this file).
#
#   benchmarks/elf-staged/run.sh            fetch, check, bench natively, emit and kernel-check
#   benchmarks/elf-staged/run.sh --native   only the native (fast-mode) part
#
# Everything is written under build/elf-staged/ (git-ignored); no binary enters the repository.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
OUT=$ROOT/build/elf-staged
MODE=${1:-all}
mkdir -p "$OUT/dl"

# The subject: ripgrep 14.1.1, the upstream x86_64 musl release (static-pie, stripped, 6.6 MB).
# The tarball digest is the one upstream publishes beside the release asset.
URL=https://github.com/BurntSushi/ripgrep/releases/download/14.1.1/ripgrep-14.1.1-x86_64-unknown-linux-musl.tar.gz
TAR_SHA256=4cf9f2741e6c465ffdb7c26f38056a59e2a2544b51f7cc128ef28337eeae4d8e
RG_SHA256=$(awk '$2 == "rg" { print $1 }' "$HERE/SHA256SUMS")
TAR=$OUT/dl/$(basename "$URL")
RG=$OUT/dl/rg
if [ ! -f "$RG" ]; then
  [ -f "$TAR" ] || curl -fsSL -o "$TAR" "$URL"
  echo "$TAR_SHA256  $TAR" | sha256sum -c --quiet
  tar -xzf "$TAR" -C "$OUT/dl" --strip-components=1 ripgrep-14.1.1-x86_64-unknown-linux-musl/rg
fi
echo "$RG_SHA256  $RG" | sha256sum -c --quiet
echo "subject: $RG ($(stat -c %s "$RG") bytes, sha256 $RG_SHA256)"

cd "$ROOT"
lake build elf-staged >/dev/null
TOOL=$ROOT/.lake/build/bin/elf-staged

# Instruction boundaries from two independent linear-sweep disassemblers.
"$HERE/boundaries-objdump.sh" "$RG" .text > "$OUT/text.objdump.tiles"
echo "objdump ($(objdump --version | head -1)): $(wc -l < "$OUT/text.objdump.tiles") tiles"
if command -v cargo >/dev/null; then
  cargo build -q --release --manifest-path "$HERE/iced-boundaries/Cargo.toml"
  read -r off size addr < <(readelf -SW "$RG" | python3 -I -c '
import re, sys
for l in sys.stdin:
    m = re.search(r"\]\s+\.text\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)", l)
    if m: print("0x" + m.group(2), "0x" + m.group(3), "0x" + m.group(1)); break')
  "$HERE/iced-boundaries/target/release/iced-boundaries" "$RG" "$off" "$size" "$addr" > "$OUT/text.iced.tiles"
  if cmp -s "$OUT/text.objdump.tiles" "$OUT/text.iced.tiles"; then
    echo "iced-x86 1.21.0: identical boundaries"
  else
    echo "iced-x86 1.21.0: boundaries differ in $(diff "$OUT/text.objdump.tiles" "$OUT/text.iced.tiles" | grep -c '^<') lines"
  fi
fi

"$TOOL" bench "$RG" "$OUT/text.objdump.tiles" | tee "$OUT/native.txt"
[ "$MODE" = --native ] && exit 0

# Paranoid mode: kernel-check each stage in its own file, so each time is that stage's cost
# over the shared prefix (imports and the 6.6 MB `include_bytes`).
"$TOOL" emit "$RG" "$OUT/Bench.lean" --tiles "$OUT/text.objdump.tiles" --tile-count 1024 \
  --rela-windows 22 --rela-window 1024 ${WHOLE:+--whole}
mkdir -p "$OUT/split"
python3 -I "$HERE/split.py" "$OUT/Bench.lean" "$OUT/split" > "$OUT/split/names.txt"
: > "$OUT/kernel.txt"
while read -r name; do
  start=$(date +%s%N)
  if lake env lean "$OUT/split/$name.lean" > "$OUT/split/$name.log" 2>&1; then st=ok; else st=FAILED; fi
  end=$(date +%s%N)
  printf '%-10s %7d ms  %s\n' "$name" $(( (end - start) / 1000000 )) "$st" | tee -a "$OUT/kernel.txt"
done < "$OUT/split/names.txt"
