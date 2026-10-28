#!/usr/bin/env bash
# Cross-check Silmaril.Numeric.Ieee754.Std's x86 profiles against this host's
# hardware. Operands come from TestFloat 3e level-1 vectors; results and flags are
# recomputed by the hardware instruction (scripts/ieee754/x86-hw-vectors.c) and
# checked with scripts/ieee754/TestFloatCheck.lean (SSE/AVX against `Isa.x86SSE`,
# x87 against `Isa.x87`).
#
# Usage: scripts/ieee754/x86-hw-check.sh TESTFLOAT_GEN OUTDIR [JOBS]
set -euo pipefail
gen=$1; out=$2; jobs=${3:-4}
repo=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "$out/vec"
hw="$out/x86-hw-vectors"
cc -O1 -mavx2 -mfma -mf16c -o "$hw" "$repo/scripts/ieee754/x86-hw-vectors.c"
manifest="$out/manifest.txt"
: > "$manifest"
modes="-rnear_even -rminMag -rmin -rmax"
run() { # isa fn genfn mode exact [genopts]
  local isa=$1 fn=$2 gfn=$3 m=$4 ex=$5
  local file="$out/vec/${fn}${m}_${ex}.txt"
  local stride=1
  case $gfn in *mulAdd) stride=32 ;; esac
  "$gen" "$gfn" "$m" | awk -v s=$stride '(NR - 1) % s == 0' | "$hw" "$fn" "$m" "$ex" > "$file"
  [ -s "$file" ] || { echo "no vectors in $file" >&2; exit 1; }
  echo "$isa $fn $m $ex 80 after $file" >> "$manifest"
}
for m in $modes; do
  for f in f32 f64; do
    for op in add sub mul div sqrt mulAdd; do run x86SSE ${f}_$op ${f}_$op "$m" notexact; done
    run x86SSE ${f}_x86min ${f}_add "$m" notexact
    run x86SSE ${f}_x86max ${f}_add "$m" notexact
    for ex in exact notexact; do run x86SSE ${f}_roundToInt ${f}_roundToInt "$m" $ex; done
    for i in i32 i64; do run x86SSE ${f}_to_$i ${f}_to_$i "$m" exact; done
    for i in i32 i64; do run x86SSE ${i}_to_$f ${i}_to_$f "$m" notexact; done
  done
  run x86SSE f32_to_f64 f32_to_f64 "$m" notexact
  run x86SSE f64_to_f32 f64_to_f32 "$m" notexact
  run x86SSE f32_to_f16 f32_to_f16 "$m" notexact
  run x86SSE f16_to_f32 f16_to_f32 "$m" notexact
  for op in add sub mul div sqrt; do run x87 extF80_$op extF80_$op "$m" notexact; done
  run x87 extF80_roundToInt extF80_roundToInt "$m" exact
done
for f in f32 f64; do
  for op in eq lt le eq_signaling lt_quiet le_quiet; do
    run x86SSE ${f}_$op ${f}_$op -rnear_even notexact
  done
done
run x87 extF80_rem extF80_rem -rnear_even notexact
run x87 extF80_eq extF80_eq -rnear_even notexact
run x87 extF80_lt extF80_lt -rnear_even notexact

split -n "r/$jobs" -d "$manifest" "$out/shard."
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
echo "x86 hardware: $(grep -c checked "$out/results.log") configurations, $total vectors, $failed failed"
exit $status
