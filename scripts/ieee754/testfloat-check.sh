#!/usr/bin/env bash
# Generate Berkeley TestFloat 3e level-1 vectors and check them against
# Silmaril.Numeric.Ieee754.Std (scripts/ieee754/TestFloatCheck.lean).
#
# Usage: scripts/ieee754/testfloat-check.sh ISA TESTFLOAT_GEN OUTDIR [JOBS] [MULADD_STRIDE]
#   ISA            sf8086SSE (gen built with SPECIALIZE_TYPE=8086-SSE), riscv (RISCV)
#                  or x87 (8086)
#   TESTFLOAT_GEN  path to testfloat_gen of that specialization
#   OUTDIR         new directory for vectors, manifests and logs (outside the repo)
#   JOBS           parallel checker processes (default 4)
#   MULADD_STRIDE  keep every N-th mulAdd vector (default 32; level 1 has 6133248
#                  mulAdd cases per format and mode)
#
# TestFloat/SoftFloat are untrusted inputs: build them outside the repository from
# pinned commits (see docs/Ieee754Std.md).
set -euo pipefail
isa=$1; gen=$2; out=$3; jobs=${4:-4}; stride=${5:-32}
repo=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "$out/vec"
manifest="$out/manifest.txt"
: > "$manifest"
modes="-rnear_even -rminMag -rmin -rmax -rnear_maxMag"
case $isa in
  x87) floats="f32 f64 extF80" ;;
  *) floats="f16 f32 f64 f128" ;;
esac
ints="i32 ui32 i64 ui64"

emit() { # name file mode exact prec tin -- gen args...
  local name=$1 file=$2 mode=$3 exact=$4 prec=$5 tin=$6; shift 6
  echo "$isa $name $mode $exact $prec $tin $file" >> "$manifest"
}
gen_to() { # file stride args...
  local file=$1 s=$2; shift 2
  if [ "$s" = 1 ]; then "$gen" "$@" > "$file"; else "$gen" "$@" | awk -v s="$s" 'NR % s == 1' > "$file"; fi
}

for f in $floats; do
  for m in $modes; do
    for op in add sub mul div sqrt; do
      file="$out/vec/${f}_${op}${m}.txt"; gen_to "$file" 1 "${f}_${op}" "$m"
      emit "${f}_${op}" "$file" "$m" notexact 80 after
      if [ "$f" = extF80 ]; then
        for p in 32 64; do
          file="$out/vec/${f}_${op}${m}_p$p.txt"; gen_to "$file" 1 -precision$p "${f}_${op}" "$m"
          emit "${f}_${op}" "$file" "$m" notexact $p after
        done
      fi
    done
    if [ "$f" != extF80 ]; then
      file="$out/vec/${f}_mulAdd${m}.txt"; gen_to "$file" "$stride" "${f}_mulAdd" "$m"
      emit "${f}_mulAdd" "$file" "$m" notexact 80 after
    fi
    for ex in notexact exact; do
      file="$out/vec/${f}_roundToInt${m}_$ex.txt"; gen_to "$file" 1 "${f}_roundToInt" "$m" -$ex
      emit "${f}_roundToInt" "$file" "$m" $ex 80 after
      for i in $ints; do
        file="$out/vec/${f}_to_${i}${m}_$ex.txt"; gen_to "$file" 1 "${f}_to_${i}" "$m" -$ex
        emit "${f}_to_${i}" "$file" "$m" $ex 80 after
      done
    done
    for g in $floats; do
      [ "$f" = "$g" ] && continue
      file="$out/vec/${f}_to_${g}${m}.txt"; gen_to "$file" 1 "${f}_to_${g}" "$m"
      emit "${f}_to_${g}" "$file" "$m" notexact 80 after
    done
    for i in $ints; do
      file="$out/vec/${i}_to_${f}${m}.txt"; gen_to "$file" 1 "${i}_to_${f}" "$m"
      emit "${i}_to_${f}" "$file" "$m" notexact 80 after
    done
  done
  # tininess before rounding (a variant; no x86/RISC-V hardware uses it)
  for op in mul div; do
    file="$out/vec/${f}_${op}_tinybefore.txt"; gen_to "$file" 1 -tininessbefore "${f}_${op}"
    emit "${f}_${op}" "$file" -rnear_even notexact 80 before
  done
  file="$out/vec/${f}_rem.txt"; gen_to "$file" 1 "${f}_rem"
  emit "${f}_rem" "$file" -rnear_even notexact 80 after
  for op in eq le lt eq_signaling le_quiet lt_quiet; do
    file="$out/vec/${f}_${op}.txt"; gen_to "$file" 1 "${f}_${op}"
    emit "${f}_${op}" "$file" -rnear_even notexact 80 after
  done
done

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
echo "$isa: $(grep -c checked "$out/results.log") configurations, $total vectors, $failed failed"
exit $status
