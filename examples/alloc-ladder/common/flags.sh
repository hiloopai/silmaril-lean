# Shared compiler/linker flags for the ELF ladder.  Sourced by each build.sh.
# Mirrors silmaril-lean apps/sha256sum-min/scripts/build.sh (GCC 13.3.0,
# binutils 2.42) with one addition:
#   -fno-tree-loop-distribute-patterns : no synthesized memcpy/memset calls
#     (belt-and-braces: GCC 13.3 -ffreestanding -fno-builtin already emits none)
#   (no -flto: each TU is compiled separately, so cross-TU calls stay calls)
# A rung may append to EXTRA_CFLAGS (e.g. rung 07 re-enables jump tables), and may
# replace BASE_CFLAGS for its subject TUs by setting SUBJECT_CFLAGS (rung 15).
LADDER_COMMON=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
CC=${CC:-gcc}
OPT=${OPT:--O2}
BASE_CFLAGS=(-std=gnu11 -ffreestanding -fno-builtin -fno-stack-protector
  -fcf-protection=none -mgeneral-regs-only -fno-pic -fno-pie
  -fno-asynchronous-unwind-tables -fno-unwind-tables -fno-jump-tables
  -fno-tree-vectorize -fno-tree-slp-vectorize -fno-bit-tests -fno-if-conversion
  -fno-if-conversion2 -fno-tree-loop-distribute-patterns
  -ffunction-sections -fdata-sections
  -fno-ident -Wall -Wextra -Wno-unused-parameter -I"$LADDER_COMMON")
# FLOAT_CFLAGS: BASE_CFLAGS without -mgeneral-regs-only, for rungs whose subject
# TUs use C float/double (rung 15).  Scalar SSE2 only: no VEX (-mno-avx), no x87
# (-mno-80387, so `long double` is a compile error), no vectorisation (already in
# BASE_CFLAGS).  The runtime TUs (rt.c, libmini.c) keep BASE_CFLAGS.  A rung selects
# it with SUBJECT_CFLAGS=("${FLOAT_CFLAGS[@]}") before ladder_rung.
FLOAT_CFLAGS=()
for f in "${BASE_CFLAGS[@]}"; do
  [ "$f" = -mgeneral-regs-only ] || FLOAT_CFLAGS+=("$f")
done
FLOAT_CFLAGS+=(-mfpmath=sse -mno-avx -mno-80387)
LDFLAGS=(-nostdlib -static -no-pie -Wl,--gc-sections -Wl,--build-id=none
  -Wl,-z,noexecstack -Wl,-z,norelro -Wl,-e,_start)

# ladder_build NAME OUTDIR SRC... : compiles each C/S source to its own object
# (one object per translation unit) and links NAME with start.o, rt.o, libmini.o.
ladder_build() {
  local name=$1 out=$2; shift 2
  mkdir -p "$out/obj"
  local objs=()
  local subj=("${BASE_CFLAGS[@]}")
  if [ -n "${SUBJECT_CFLAGS+x}" ]; then subj=("${SUBJECT_CFLAGS[@]}"); fi
  $CC -c "$LADDER_COMMON/start.S" -o "$out/obj/start.o"
  $CC "$OPT" "${BASE_CFLAGS[@]}" -c "$LADDER_COMMON/rt.c" -o "$out/obj/rt.o"
  $CC "$OPT" "${BASE_CFLAGS[@]}" -c "$LADDER_COMMON/libmini.c" -o "$out/obj/libmini.o"
  for src in "$@"; do
    local base; base=$(basename "${src%.*}")
    case "$src" in
      *.S) $CC -c "$src" -o "$out/obj/$base.o" ;;
      *)   $CC "$OPT" "${subj[@]}" ${EXTRA_CFLAGS[@]+"${EXTRA_CFLAGS[@]}"} -c "$src" -o "$out/obj/$base.o" ;;
    esac
    objs+=("$out/obj/$base.o")
  done
  $CC "${LDFLAGS[@]}" "$out/obj/start.o" "$out/obj/rt.o" "$out/obj/libmini.o" "${objs[@]}" -o "$out/$name"
  objdump -d --no-show-raw-insn "$out/$name" > "$out/$name.dis"
}

# ladder_rung DIR NAME SRC... : builds NAME at -O1 and -O2 under DIR/build/<opt>,
# runs it (stdin from $RUN_STDIN if set, else /dev/null) and requires exit 0.
# Set OPTS to override the optimisation levels.
ladder_rung() {
  local dir=$1 name=$2; shift 2
  local o
  for o in ${OPTS:--O1 -O2}; do
    local out="$dir/build/${o#-}"
    rm -rf "$out"
    OPT=$o ladder_build "$name" "$out" "$@"
    local in=${RUN_STDIN:-/dev/null}
    if ! "$out/$name" < "$in" > "$out/run.out" 2> "$out/run.err"; then
      echo "$name ($o): self-test FAILED" >&2; cat "$out/run.out" "$out/run.err" >&2; return 1
    fi
    if [ -n "${EXPECT_STDOUT:-}" ] && ! cmp -s "$out/run.out" "$EXPECT_STDOUT"; then
      echo "$name ($o): stdout differs from $EXPECT_STDOUT" >&2; return 1
    fi
    echo "$name ($o): $(tail -c 200 "$out/run.out" | tr '\n' ' ')"
  done
}
