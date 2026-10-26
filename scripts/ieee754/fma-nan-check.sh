#!/usr/bin/env bash
# Check every Berkeley TestFloat 3e level-1 mulAdd vector with a NaN operand
# (no stride), in all five rounding directions, against
# Silmaril.Numeric.Ieee754.Std (scripts/ieee754/TestFloatCheck.lean).
# testfloat-check.sh and x86-hw-check.sh keep only every 32nd mulAdd vector; this
# pass covers the NaN-propagation cases of fma completely.
#
# ISA x86hw recomputes the results and flags of those operands on this host's
# hardware (scripts/ieee754/x86-hw-vectors.c: VFMADD213/132/231, which must agree)
# and checks them against `Isa.x86SSE` (f32 and f64, the four x86 rounding
# directions); TESTFLOAT_GEN is then the 8086-SSE testfloat_gen, used for operands.
#
# Usage: scripts/ieee754/fma-nan-check.sh ISA TESTFLOAT_GEN OUTDIR "FORMATS"
#   ISA            sf8086SSE, riscv or x87 (as in testfloat-check.sh), or x86hw
#   TESTFLOAT_GEN  testfloat_gen of that specialization
#   OUTDIR         new directory outside the repo
#   FORMATS        among f16 f32 f64 f128 (x87: f32 f64)
set -euo pipefail
isa=$1; gen=$2; out=$3; formats=$4
repo=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "$out/vec"
: > "$out/manifest.txt"
modes="-rnear_even -rminMag -rmin -rmax -rnear_maxMag"
filter=cat
tag=$isa
if [ "$isa" = x86hw ]; then
  cc -O1 -mavx2 -mfma -mf16c -o "$out/x86-hw-vectors" "$repo/scripts/ieee754/x86-hw-vectors.c"
  modes="-rnear_even -rminMag -rmin -rmax"
  tag=x86SSE
fi
for f in $formats; do
  case $f in
    f16) inf=7C00 ;; f32) inf=7F800000 ;; f64) inf=7FF0000000000000 ;;
    f128) inf=7FFF0000000000000000000000000000 ;;
    *) echo "unknown format $f" >&2; exit 2 ;;
  esac
  for m in $modes; do
    [ "$isa" = x86hw ] && filter="$out/x86-hw-vectors ${f}_mulAdd $m notexact"
    # A NaN operand: its magnitude (sign bit cleared) exceeds the infinity's.
    "$gen" -level 1 "${f}_mulAdd" "$m" | awk -v inf="$inf" '
      function mag(x,  d) { d = index("0123456789ABCDEF", substr(x, 1, 1)) - 1; if (d >= 8) d -= 8
        return substr("0123456789ABCDEF", d + 1, 1) substr(x, 2) }
      function nan(x) { return mag(x) > inf }
      { if (nan($1) || nan($2) || nan($3)) print }' | $filter > "$out/vec/${f}_nan$m.txt"
    echo "$tag ${f}_mulAdd $m notexact 80 after $out/vec/${f}_nan$m.txt" >> "$out/manifest.txt"
  done
done
split -n r/4 -d "$out/manifest.txt" "$out/shard."
cd "$repo"
pids=()
for s in "$out"/shard.*; do
  lake env lean --run scripts/ieee754/TestFloatCheck.lean "$s" > "$s.log" 2>&1 &
  pids+=($!)
done
status=0
for p in "${pids[@]}"; do wait "$p" || status=1; done
cat "$out"/shard.*.log > "$out/results.log"
total=$(awk '/checked/ {c += $(NF-2)} END {print c}' "$out/results.log")
failed=$(awk '/checked/ {c += $NF} END {print c}' "$out/results.log")
echo "$isa fma NaN operands: $(grep -c checked "$out/results.log") configurations, $total vectors, $failed failed"
exit $status
