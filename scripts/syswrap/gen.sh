#!/usr/bin/env bash
# Regenerate the glibc system call wrapper modules (Silmaril/Libc/SysWrap/Glibc/V*/{Defs,Thms}.lean)
# and their reports (tools/syswrap-gen/data/<pin>.report.tsv) from the pinned libc.so.6 files.
#   scripts/syswrap/gen.sh DIR           DIR holds <pin>/libc.so.6 for the three pins below
#   scripts/syswrap/gen.sh DIR --check   regenerate, then fail if a generated file changed
# The files are checked against their sha256 first (the packages are named in
# NOTICES/glibc-syswrap/README.md).
set -euo pipefail
here=$(cd "$(dirname "$0")/../.." && pwd)
dir=${1:?usage: $0 DIR [--check]}
mode=${2:-write}
cd "$here"
cargo build --release -q --manifest-path tools/syswrap-gen/Cargo.toml
gen=tools/syswrap-gen/target/release/syswrap-gen
pins=(
  "debian_2_36_9_deb12u14 V236 6b4a45352fd0c540a9c7c718f35ce8c8e46a4e482f9d3885a910c32d1a0e1421 glibc 2.36 (Debian 12 libc6 2.36-9+deb12u14)"
  "ubuntu_2_39_0ubuntu8_9 V239 3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf glibc 2.39 (Ubuntu 24.04 libc6 2.39-0ubuntu8.9)"
  "ubuntu_2_40_1ubuntu3_1 V240 132ba50d4abaeff314e64f5d84daa4e4e6d9b227135bc035fde1b69a81aab204 glibc 2.40 (Ubuntu 24.10 libc6 2.40-1ubuntu3.1)"
)
out=()
for row in "${pins[@]}"; do
  read -r pin v sha title <<<"$row"
  lib="$dir/$pin/libc.so.6"
  echo "$sha  $lib" | sha256sum -c --quiet - || { echo "gen.sh: $lib: sha256 mismatch" >&2; exit 1; }
  m=Silmaril/Libc/SysWrap/Glibc/$v
  mkdir -p "$m"
  "$gen" --lib "$lib" --pin "$pin" --title "$title" --namespace "Silmaril.Libc.SysWrap.Glibc.$v" \
    --symbols "tools/syswrap-gen/data/$pin.symbols" --syscalls tools/syswrap-gen/data/x86_64-syscalls.tsv \
    --defs "$m/Defs.lean" --defs-module "Silmaril.Libc.SysWrap.Glibc.$v.Defs" --thms "$m/Thms.lean" \
    --report "tools/syswrap-gen/data/$pin.report.tsv"
  out+=("$m/Defs.lean" "$m/Thms.lean" "tools/syswrap-gen/data/$pin.report.tsv")
done
if [ "$mode" = --check ]; then
  git diff --exit-code -- "${out[@]}" || { echo "gen.sh: the generated files are stale (above)" >&2; exit 1; }
fi
