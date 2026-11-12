#!/usr/bin/env bash
# Differential test of `wasm-tools addr2line` against the pinned wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/addr2line/differential.sh [--ours BIN] [--keep DIR]
#
# Inputs: when $WT_CAT_DEBUG names the pinned debug build of the corpus' cat.wasm (pins.sh), its
# Rust core module (DWARF 4, inlining) and the component itself (a nested module); when the
# pinned wasi-sdk 27 is installed at $WASI_SDK (pins.sh), the C and C++ samples of this
# directory compiled with -gdwarf-4/-gdwarf-5 at -O0/-O2. Skips when there is neither. For each input, one invocation with many addresses across its
# code sections (stdout compared byte for byte), the same with --code-section-relative, and
# error cases (stdout, stderr and exit code compared exactly; the WAT parser's message on text input
# by class). Skips when the pinned wasm-tools
# is absent; exit 1 when any case differs.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
# shellcheck source=pins.sh
source "$here/../pins.sh"
WT=$WT_UPSTREAM
SDK=$WASI_SDK
OURS=$root/.lake/build/bin/wasm-tools
KEEP=
while [[ $# -gt 0 ]]; do
  case $1 in
    --ours) OURS=$2; shift 2 ;; --keep) KEEP=$2; shift 2 ;;
    *) echo "usage: $0 [--ours BIN] [--keep DIR]" >&2; exit 2 ;;
  esac
done
wt_require_upstream
wt_require_ours "$OURS" wasm-tools
unset COLUMNS
d=${KEEP:-$(mktemp -d)}
mkdir -p "$d"
pass=0; fail=0; failures=()

inputs=()
cat_debug=$(wt_cat_debug) || exit 1
if [[ -n $cat_debug ]]; then
  cp "$cat_debug" "$d/cat-debug.wasm"
  python3 -I - "$d/cat-debug.wasm" "$d/cat-debug-core.wasm" <<'PY'
import sys
b = open(sys.argv[1], "rb").read()
def leb(b, i):
    r = s = 0
    while True:
        x = b[i]; i += 1; r |= (x & 127) << s; s += 7
        if x < 128: return r, i
i = 8
while i < len(b):
    sid = b[i]; i += 1; n, i = leb(b, i)
    if sid == 1:
        open(sys.argv[2], "wb").write(b[i:i + n]); break
    i += n
PY
  inputs+=("cat-debug-core.wasm:37" "cat-debug.wasm:211")
else
  echo "note: WT_CAT_DEBUG unset; the cat-debug inputs are skipped (see pins.sh)"
fi
if [[ -x $SDK/bin/clang ]]; then
  for v in 4 5; do for o in 0 2; do
    "$SDK/bin/clang++" --target=wasm32-wasip1 --sysroot="$SDK/share/wasi-sysroot" -gdwarf-$v -O$o \
      -nostartfiles -Wl,--no-entry -Wl,--export=entry -o "$d/cpp-d$v-O$o.wasm" "$here/sample.cpp" &&
      inputs+=("cpp-d$v-O$o.wasm:1")
    "$SDK/bin/clang" --target=wasm32-wasip1 --sysroot="$SDK/share/wasi-sysroot" -gdwarf-$v -O$o \
      -nostartfiles -Wl,--no-entry -Wl,--export=entry -o "$d/c-d$v-O$o.wasm" "$here/sample.c" &&
      inputs+=("c-d$v-O$o.wasm:1")
  done; done
else
  echo "note: wasi-sdk 27 not installed at $SDK; C and C++ inputs skipped"
fi
if [[ ${#inputs[@]} -eq 0 ]]; then
  echo "SKIP: no DWARF input (set WT_CAT_DEBUG, or install wasi-sdk: fetch-pins.sh wasi-sdk)"
  exit 0
fi

# run NAME ARGS...: compare stdout, stderr and exit code exactly.
run() {
  local name=$1; shift
  "$WT" "$@" > "$d/up.out" 2> "$d/up.err" < /dev/null; local ru=$?
  "$OURS" "$@" > "$d/our.out" 2> "$d/our.err" < /dev/null; local ro=$?
  local why=
  [[ $ru == "$ro" ]] || why="exit $ru vs $ro"
  [[ -z $why ]] && ! cmp -s "$d/up.out" "$d/our.out" && why="stdout differs ($(diff "$d/up.out" "$d/our.out" | grep -c '^<') lines)"
  if [[ $name == *"(class)" ]]; then
    [[ -z $why ]] && ! head -c 6 "$d/our.err" | grep -q '^error' && why="stderr class"
  else
    [[ -z $why ]] && ! cmp -s "$d/up.err" "$d/our.err" && why="stderr differs"
  fi
  if [[ -z $why ]]; then pass=$((pass+1)); else fail=$((fail+1)); failures+=("$name: $why"); cp "$d/up.out" "$d/$name.up"; cp "$d/our.out" "$d/$name.our"; fi
}

total=0
for spec in "${inputs[@]}"; do
  f=${spec%%:*}; step=${spec##*:}
  mapfile -t A < <(python3 -I "$here/addrs.py" "$d/$f" "$step")
  total=$((total + ${#A[@]}))
  run "$f-addresses" addr2line "$d/$f" "${A[@]}"
  if [[ $f != cat-debug.wasm ]]; then
    mapfile -t R < <(python3 -I "$here/addrs.py" "$d/$f" "$((step * 5))" --relative)
    total=$((total + ${#R[@]}))
    run "$f-relative" addr2line --code-section-relative "$d/$f" "${R[@]}"
  fi
done
f=${inputs[0]%%:*}
[[ $f == cat-debug.wasm ]] && f=cat-debug-core.wasm
run "error: below code" addr2line "$d/$f" 0x100
run "error: past module" addr2line "$d/$f" 0x5000000
run "error: bad hex" addr2line "$d/$f" 0xzz
run "error: empty" addr2line "$d/$f" ""
run "error: too large" addr2line "$d/$f" 123456789012345678901234
run "plus sign" addr2line "$d/$f" 0x+3f00 +16128
run "partial output then error" addr2line "$d/$f" 0x3f00 0x100 0x3f01
run "no addresses" addr2line "$d/$f"
run "-o file" addr2line "$d/$f" 0x3f00 -o "$d/o.txt"
[[ -f $d/cat-debug.wasm ]] &&
  run "relative in component" addr2line --code-section-relative "$d/cat-debug.wasm" 10
run "not wasm: the WAT parser's message (class)" addr2line "$here/addrs.py" 0x10
wt_corpus_check
run "no dwarf" addr2line "$WT_CORPUS_DIR/cat.wasm" 0x2000
run "usage: suggestion" addr2line --code-section-relativ
run "usage: unknown" addr2line --foo
run "usage: two -g" addr2line -g -g
run "usage: positional then suggestion" addr2line a b --cde

echo "addr2line differential: $pass passed, $fail failed ($total addresses over ${#inputs[@]} inputs; work dir $d)"
for x in "${failures[@]}"; do echo "  FAIL $x"; done
[[ -z $KEEP ]] && rm -rf "$d"
[[ $fail == 0 ]]
