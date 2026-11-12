#!/usr/bin/env bash
# Differential test of `wasm-tools dump` against the pinned wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/dump-diff.sh [--jobs N] [--out DIR] [--quick]
#
# Corpus: the binaries of every `.wast` of the WebAssembly/spec test/core pin (if unpacked, see
# pins.sh), converted by the pinned `json-from-wast`; every `.wat`/`.wast` under wasm-tools'
# tests/cli (when its source is unpacked: `.wat` files assembled by the pinned `parse`, `.wast`
# files converted); the binaries of `wt_corpus_wasm` (pins.sh). `--quick`: only those binaries
# and tests/cli/dump*.
#
# For each binary both tools run `dump FILE`. A case agrees when both succeed with byte-identical
# stdout, or both fail. Results: DIR/results.tsv (kind, file, upstream status, ours, verdict),
# a summary per kind (module/component). Exit status 0 when the number of disagreements is at
# most the bound in dump-baseline.txt, 1 otherwise; skips (status 0) without the
# pinned wasm-tools or our binary ($WASM_TOOLS_OURS, default .lake/build/bin/wasm-tools).

set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
# shellcheck source=pins.sh
source "$here/pins.sh"
wt_require_upstream

jobs=4
out=""
quick=0
while [[ $# -gt 0 ]]; do
  case $1 in
    --jobs) jobs=$2; shift 2 ;;
    --out) out=$2; shift 2 ;;
    --quick) quick=1; shift ;;
    *) echo "usage: $0 [--jobs N] [--out DIR] [--quick]" >&2; exit 2 ;;
  esac
done

ours=${WASM_TOOLS_OURS:-$repo/.lake/build/bin/wasm-tools}
wt_require_ours "$ours" wasm-tools
out=${out:-$(mktemp -d /tmp/wasm-tools-dump-diff.XXXXXX)}
mkdir -p "$out/corpus"
cases=$out/cases.txt
: > "$cases"

convert() {
  local wast=$1 tag=$2 dir
  dir=$out/corpus/$tag
  mkdir -p "$dir"
  if (cd "$dir" && "$WT_UPSTREAM" json-from-wast "$wast" -o "$dir/x.json" --wasm-dir "$dir" \
      >/dev/null 2>&1); then
    for f in "$dir"/*.wasm; do
      [[ -e $f ]] && printf '%s\n' "$f" >> "$cases"
    done
  fi
  return 0
}

assemble() {
  local wat=$1 tag=$2
  mkdir -p "$out/corpus/wat"
  if "$WT_UPSTREAM" parse "$wat" -o "$out/corpus/wat/$tag.wasm" >/dev/null 2>&1; then
    printf '%s\n' "$out/corpus/wat/$tag.wasm" >> "$cases"
  fi
  return 0
}

cli=$WT_SRC_DIR/tests/cli
if [[ $quick -eq 0 ]]; then
  if [[ -d $WASM_SPEC_DIR ]]; then
    while IFS= read -r w; do
      rel=${w#"$WASM_SPEC_DIR"/}
      convert "$w" "spec/${rel//\//_}"
    done < <(find "$WASM_SPEC_DIR" -name '*.wast' | sort)
  else
    echo "note: $WASM_SPEC_DIR absent, spec corpus skipped" >&2
  fi
  if [[ -d $cli ]]; then
    while IFS= read -r w; do
      rel=${w#"$cli"/}
      convert "$w" "cli/${rel//\//_}"
    done < <(find "$cli" -name '*.wast' | sort)
    while IFS= read -r w; do
      rel=${w#"$cli"/}
      assemble "$w" "${rel//\//_}"
    done < <(find "$cli" -name '*.wat' | sort)
  fi
elif [[ -d $cli ]]; then
  while IFS= read -r w; do
    rel=${w#"$cli"/}
    assemble "$w" "${rel//\//_}"
  done < <(find "$cli" -path '*dump*' -name '*.wat' | sort)
fi
wt_corpus_wasm | while IFS= read -r f; do
  printf '%s\n' "$f" >> "$cases"
done
echo "corpus: $(wc -l < "$cases") binaries" >&2

run_case() {
  local f=$1 kind=module uo oo us os verdict name
  if [[ $(head -c 8 "$f" | od -An -tx1 | tr -d ' \n') == 0061736d0d000100 ]]; then kind=component; fi
  uo=$(mktemp); oo=$(mktemp)
  set +e
  timeout 120 "$WT_UPSTREAM" dump "$f" > "$uo" 2>/dev/null; us=$?
  timeout 120 "$ours" dump "$f" > "$oo" 2>/dev/null; os=$?
  set -e
  if [[ $us -eq 0 && $os -eq 0 ]]; then
    if cmp -s "$uo" "$oo"; then verdict=agree; else verdict=stdout-differs; fi
  elif [[ $us -ne 0 && $os -ne 0 ]]; then verdict=agree
  elif [[ $us -eq 0 ]]; then verdict=ours-rejects
  else verdict=ours-accepts
  fi
  rm -f "$uo" "$oo"
  name=$f
  case $f in
    "$OUT"/corpus/*) name=${f#"$OUT"/corpus/} ;;
    "$REPO"/*) name=repo/${f#"$REPO"/} ;;
    "$SIL_TOOLS"/*) name=pins/${f#"$SIL_TOOLS"/} ;;
  esac
  printf '%s\t%s\t%s\t%s\t%s\n' "$kind" "$name" "$us" "$os" "$verdict"
}
export -f run_case
OUT=$out
REPO=$repo
export WT_UPSTREAM ours OUT REPO SIL_TOOLS

results=$out/results.tsv
xargs -P "$jobs" -d '\n' -n 1 bash -c 'run_case "$1"' _ < "$cases" > "$results"
echo "results: $results" >&2
awk -F'\t' '{ n[$1]++; v[$1 "\t" $5]++ }
  END { for (k in n) { printf "%s\t%d", k, n[k];
    split("agree ours-rejects ours-accepts stdout-differs", vs, " ");
    for (i = 1; i <= 4; i++) printf "\t%s=%d", vs[i], v[k "\t" vs[i]] + 0; printf "\n" } }' \
  "$results" | sort

bad=$(awk -F'\t' '$5 != "agree"' "$results" | wc -l)
bound=$(grep -v '^#' "$here/dump-baseline.txt" 2>/dev/null | head -1 || true)
if [[ -n $bound && $bad -gt $bound ]]; then
  echo "disagreements: $bad, above the bound $bound (dump-baseline.txt)" >&2
  exit 1
fi
echo "disagreements: $bad (bound ${bound:-none})" >&2
exit 0
