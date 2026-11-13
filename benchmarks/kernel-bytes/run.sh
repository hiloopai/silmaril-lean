#!/usr/bin/env bash
# Run the kernel-bytes benchmarks; prints `size<TAB>step<TAB>ms` lines.
#   benchmarks/kernel-bytes/run.sh 1048576 4194304 16777216
# Append `native` to a size (e.g. 1048576:native) to also time native runs, which compile the
# data (computable `kbytes_def`).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../.."
lake build Silmaril.Prelude.Bytes.Elab.Defs Silmaril.Prelude.Bytes.Native.Defs >/dev/null
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp "$here/Bench.lean" "$work/Bench.lean"
LEAN_PATH="$(lake env printenv LEAN_PATH)"
work=$(cd "$work" && pwd)
export LEAN_PATH="$LEAN_PATH:$work"
(cd "$work" && lean --root=. -o Bench.olean Bench.lean)
for spec in "$@"; do
  n=${spec%%:*}; native=""; [ "$spec" != "$n" ] && native=1
  "$here/gen.sh" "$n" "$native" > "$work/B$n.lean"
  start=$(date +%s%N)
  (cd "$work" && lean "B$n.lean") 2>&1 | grep -o 'BENCH.*' | sed "s/^BENCH/$n/"
  echo -e "$n\twhole file (lean process)\t$(( ($(date +%s%N) - start) / 1000000 ))"
done
