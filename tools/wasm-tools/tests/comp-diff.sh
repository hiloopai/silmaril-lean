#!/usr/bin/env bash
# Differential test of component validation (`wasm-tools validate` on components) against
# wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/comp-diff.sh [--jobs N] [--out DIR] [--list]
#
# Corpus: every `.wast` of wasm-tools 1.262.0's tests/cli/component-model (with the `-f`/
# `--features` flags of its RUN line) and of the component-model test suite (unpacked at
# $SIL_TOOLS/src/component-model, run with the default features), converted to binaries
# by the pinned `json-from-wast`; only component binaries are kept (core modules are covered by
# diff.sh). Both tools run `validate [-f FLAGS] FILE`; a case agrees when the exit statuses agree
# (0 / non-zero). Results in DIR/results.tsv (file, flags, upstream status, ours, verdict).
# `--list` prints every disagreement. The binary under test is $WASM_TOOLS_OURS (default
# .lake/build/bin/wasm-tools). Exit status 0 when the number of disagreements is at most the
# bound in comp-baseline.txt, 1 otherwise; skips (status 0) without the pinned wasm-tools.

set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
# shellcheck source=pins.sh
source "$here/pins.sh"
wt_require_upstream

jobs=4
out=""
list=0
while [[ $# -gt 0 ]]; do
  case $1 in
    --jobs) jobs=$2; shift 2 ;;
    --out) out=$2; shift 2 ;;
    --list) list=1; shift ;;
    *) echo "usage: $0 [--jobs N] [--out DIR] [--list]" >&2; exit 2 ;;
  esac
done

ours=${WASM_TOOLS_OURS:-$repo/.lake/build/bin/wasm-tools}
wt_require_ours "$ours" wasm-tools
cm_cli=$WT_SRC_DIR/tests/cli/component-model
cm_suite=$SIL_TOOLS/src/component-model/test
if [[ ! -d $cm_cli && ! -d $cm_suite ]]; then
  echo "SKIP: no component test sources under $SIL_TOOLS/src" >&2
  exit 0
fi
out=${out:-$(mktemp -d /tmp/wasm-tools-comp-diff.XXXXXX)}
mkdir -p "$out/corpus"
cases=$out/cases.txt
: > "$cases"

convert() {
  local wast=$1 tag=$2 flags=$3 dir f
  dir=$out/corpus/$tag
  mkdir -p "$dir"
  if (cd "$dir" && "$WT_UPSTREAM" json-from-wast "$wast" -o "$dir/x.json" --wasm-dir "$dir" \
      >/dev/null 2>&1); then
    for f in "$dir"/*.wasm; do
      [[ -e $f ]] || continue
      if [[ $(head -c 8 "$f" | od -An -tx1 | tr -d ' \n') == 0061736d0d000100 ]]; then
        printf '%s\t%s\n' "$f" "$flags" >> "$cases"
      fi
    done
  fi
  return 0
}

if [[ -d $cm_cli ]]; then
  while IFS= read -r w; do
    run=$(grep -m1 '^;; RUN' "$w" || true)
    flags=$(sed -n 's/.* -f \([^ ]*\).*/\1/p; s/.*--features=\([^ ]*\).*/\1/p' <<< "$run" | head -1)
    rel=${w#"$cm_cli"/}
    convert "$w" "cli/${rel//\//_}" "$flags"
  done < <(find "$cm_cli" -name '*.wast' | sort)
fi
if [[ -d $cm_suite ]]; then
  while IFS= read -r w; do
    rel=${w#"$cm_suite"/}
    convert "$w" "cm/${rel//\//_}" ""
  done < <(find "$cm_suite" -name '*.wast' | sort)
fi
echo "corpus: $(wc -l < "$cases") component binaries" >&2

run_case() {
  local f=$1 flags=$2 us os verdict
  local -a fa=()
  if [[ -n $flags ]]; then fa=(-f "$flags"); fi
  set +e
  "$WT_UPSTREAM" validate "${fa[@]}" "$f" >/dev/null 2>&1; us=$?
  timeout 60 "$ours" validate "${fa[@]}" "$f" >/dev/null 2>&1; os=$?
  set -e
  if [[ $us -eq 0 && $os -eq 0 ]] || [[ $us -ne 0 && $os -ne 0 ]]; then verdict=agree
  elif [[ $us -eq 0 ]]; then verdict=ours-rejects
  else verdict=ours-accepts
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "${f#"$OUT"/corpus/}" "$flags" "$us" "$os" "$verdict"
}
export -f run_case
OUT=$out
export WT_UPSTREAM ours OUT

results=$out/results.tsv
tr '\t' '\n' < "$cases" | paste - - | \
  xargs -P "$jobs" -d '\n' -n 1 bash -c 'IFS=$'"'"'\t'"'"' read -r f fl <<< "$1"; run_case "$f" "$fl"' _ \
  | sort > "$results"

echo "results: $results" >&2
awk -F'\t' '{ n++; v[$5]++; if ($3 == 0) valid++ }
  END { printf "components %d (upstream valid %d): agree=%d ours-rejects=%d ours-accepts=%d\n",
    n, valid, v["agree"], v["ours-rejects"], v["ours-accepts"] }' "$results"
if [[ $list -eq 1 ]]; then awk -F'\t' '$5 != "agree"' "$results"; fi

bound=$(grep -v '^#' "$here/comp-baseline.txt" 2>/dev/null | head -1 || true)
bad=$(awk -F'\t' '$5 != "agree"' "$results" | wc -l)
if [[ -n $bound && $bad -gt $bound ]]; then
  echo "disagreements: $bad, above the baseline bound $bound (comp-baseline.txt)" >&2
  exit 1
fi
exit 0
