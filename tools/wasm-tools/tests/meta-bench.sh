#!/usr/bin/env bash
# Benchmark (and performance regression test) of the meta subcommands (demangle, metadata,
# addr2line) against the pinned
# wasm-tools 1.262.0, on inputs from about 100 bytes to 3 MB.
#
#   tools/wasm-tools/tests/meta-bench.sh [--ours BIN] [--runs N] [--limit SECONDS]
#
# Prints, per input and command, the best wall time of N runs (default 3) and the peak RSS of
# both binaries. Fails (exit 1) when one of our runs takes longer than --limit seconds
# (default 5) on any input: the regression bound. Skips when the pinned binary is absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
# shellcheck source=pins.sh
source "$here/pins.sh"
WT=$WT_UPSTREAM
OURS=$root/.lake/build/bin/wasm-tools
RUNS=3; LIMIT=5
while [[ $# -gt 0 ]]; do
  case $1 in
    --ours) OURS=$2; shift 2 ;; --runs) RUNS=$2; shift 2 ;; --limit) LIMIT=$2; shift 2 ;;
    *) echo "usage: $0 [--ours BIN] [--runs N] [--limit SECONDS]" >&2; exit 2 ;;
  esac
done
wt_require_upstream
wt_require_ours "$OURS" wasm-tools
d=$(mktemp -d)
# Inputs: a tiny module, the 47 KB component tests/corpus/cat.wasm and, when $WT_CAT_DEBUG is set
# (pins.sh), its 3.1 MB debug build and the 3.1 MB core module (Rust, DWARF, name section) inside
# it; without it the large inputs and the addr2line runs are skipped.
printf '(module (func $_ZN4rustE) (@producers (language "Rust" "")))' > "$d/tiny.wat"
"$WT" parse "$d/tiny.wat" -o "$d/tiny.wasm"
wt_corpus_check
cp "$WT_CORPUS_DIR/cat.wasm" "$d/cat.wasm"
cat_debug=$(wt_cat_debug) || exit 1
files=(tiny.wasm cat.wasm)
if [[ -n $cat_debug ]]; then
cp "$cat_debug" "$d/cat-debug.wasm"
files+=(cat-debug.wasm cat-debug-core.wasm)
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
else
  echo "note: WT_CAT_DEBUG unset; the cat-debug inputs and the addr2line runs are skipped"
fi
best() { # best wall time (s) and max RSS (KB) of RUNS runs
  local t m bt=999 bm=0
  for _ in $(seq "$RUNS"); do
    /usr/bin/time -f "%e %M" -o "$d/t" "$@" > /dev/null 2>&1
    read -r t m < <(tail -1 "$d/t")
    bt=$(awk -v a="$t" -v b="$bt" 'BEGIN{print (a<b)?a:b}'); bm=$(( m > bm ? m : bm ))
  done
  echo "$bt $bm"
}
bad=0
printf '%-18s %-30s %10s %10s %10s %10s\n' input command "ours(s)" "ours(MB)" "up(s)" "up(MB)"
for f in "${files[@]}"; do
  for c in "demangle" "metadata show" "metadata show --json" "metadata add --name x --language a=1"; do
    read -r ot om < <(best "$OURS" $c "$d/$f" -o "$d/o")
    read -r ut um < <(best "$WT" $c "$d/$f" -o "$d/o")
    printf '%-18s %-30s %10s %10s %10s %10s\n' "$f" "$c" "$ot" "$((om/1024))" "$ut" "$((um/1024))"
    awk -v a="$ot" -v l="$LIMIT" 'BEGIN{exit !(a>l)}' && { echo "  REGRESSION: over ${LIMIT}s"; bad=1; }
  done
done
# addr2line: one address, and every 37th byte of the code section (about 4300 addresses).
[[ -n $cat_debug ]] && mapfile -t A < <(python3 -I "$here/addr2line/addrs.py" "$d/cat-debug-core.wasm" 37)
for set in one many; do
  [[ -n $cat_debug ]] || break
  if [[ $set == one ]]; then args=(0x3f00); else args=("${A[@]}"); fi
  read -r ot om < <(best "$OURS" addr2line "$d/cat-debug-core.wasm" "${args[@]}")
  read -r ut um < <(best "$WT" addr2line "$d/cat-debug-core.wasm" "${args[@]}")
  printf '%-18s %-30s %10s %10s %10s %10s\n' "cat-debug-core" "addr2line ($set: ${#args[@]})" "$ot" "$((om/1024))" "$ut" "$((um/1024))"
  awk -v a="$ot" -v l="$LIMIT" 'BEGIN{exit !(a>l)}' && { echo "  REGRESSION: over ${LIMIT}s"; bad=1; }
done
# metadata show of a module whose .dep-v0 section inflates to the 2 MiB limit.
python3 -I "$here/depv0-cases.py" "$d" && "$WT" parse "$d/dep-ok-limit.wat" -o "$d/dep-ok-limit.wasm"
read -r ot om < <(best "$OURS" metadata show "$d/dep-ok-limit.wasm")
read -r ut um < <(best "$WT" metadata show "$d/dep-ok-limit.wasm")
printf '%-18s %-30s %10s %10s %10s %10s\n' "dep-v0 2 MiB" "metadata show" "$ot" "$((om/1024))" "$ut" "$((um/1024))"
awk -v a="$ot" -v l="$LIMIT" 'BEGIN{exit !(a>l)}' && { echo "  REGRESSION: over ${LIMIT}s"; bad=1; }
rm -rf "$d"
exit $bad
