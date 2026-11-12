#!/usr/bin/env bash
# Differential test of the validate track (validate, strip, objdump) against wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/diff.sh [--jobs N] [--out DIR] [--quick] [--sweep] [--no-baseline]
#
# Corpus: every `.wast` under the WebAssembly/spec test/core pin (if unpacked, see pins.sh) and
# wasm-tools' own tests/cli/missing-features (with the `-f` flags of their RUN lines) when its
# source is unpacked, all converted to binaries by the pinned `wasm-tools json-from-wast`, plus
# the binaries of `wt_corpus_wasm` (pins.sh: the vendored tests/corpus, tests/fixtures, the
# fetched WASI adapters, the wave-1 tools' test inputs). `--quick`: only those binaries. `--sweep`: instead of the default invocations, run
# `validate -f G` for each feature group G (wasm1, wasm2, wasm3, lime1, mvp, all, -all).
#
# For each binary and each invocation (`validate [-f FLAGS]`, `objdump`, `strip`, `strip -a`) both
# tools run with the same arguments; a case agrees when the exit statuses agree (0 / non-zero) and,
# on success, stdout is byte-identical. Results go to DIR/results.tsv (kind, file, invocation,
# upstream status, our status, verdict); a summary is printed. The binary under test is
# $WASM_TOOLS_OURS (default .lake/build/bin/wasm-tools, the lean_exe `wasm-tools`).
#
# Exit status 0 when every disagreement is listed in tools/wasm-tools/tests/known-diffs.txt
# (or with --no-baseline), 1 otherwise. Skips (status 0) when the pinned wasm-tools is absent.

set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
# shellcheck source=pins.sh
source "$here/pins.sh"
wt_require_upstream

jobs=4
out=""
quick=0
baseline=1
sweep=0
while [[ $# -gt 0 ]]; do
  case $1 in
    --jobs) jobs=$2; shift 2 ;;
    --out) out=$2; shift 2 ;;
    --quick) quick=1; shift ;;
    --no-baseline) baseline=0; shift ;;
    --sweep) sweep=1; shift ;;
    *) echo "usage: $0 [--jobs N] [--out DIR] [--quick] [--no-baseline]" >&2; exit 2 ;;
  esac
done

ours=${WASM_TOOLS_OURS:-$repo/.lake/build/bin/wasm-tools}
wt_require_ours "$ours" wasm-tools
out=${out:-$(mktemp -d /tmp/wasm-tools-diff.XXXXXX)}
mkdir -p "$out/corpus"
cases=$out/cases.txt
: > "$cases"

# Convert one .wast (with optional validate flags) into binaries; append "file<TAB>flags" lines.
convert() {
  local wast=$1 tag=$2 flags=$3 dir
  dir=$out/corpus/$tag
  mkdir -p "$dir"
  if (cd "$dir" && "$WT_UPSTREAM" json-from-wast "$wast" -o "$dir/x.json" --wasm-dir "$dir" \
      >/dev/null 2>&1); then
    for f in "$dir"/*.wasm; do
      [[ -e $f ]] && printf '%s\t%s\n' "$f" "$flags" >> "$cases"
    done
  fi
  return 0
}

if [[ $quick -eq 0 ]]; then
  if [[ -d $WASM_SPEC_DIR ]]; then
    while IFS= read -r w; do
      rel=${w#"$WASM_SPEC_DIR"/}
      convert "$w" "spec/${rel//\//_}" ""
    done < <(find "$WASM_SPEC_DIR" -name '*.wast' | sort)
  else
    echo "note: $WASM_SPEC_DIR absent, spec corpus skipped" >&2
  fi
  mf=$WT_SRC_DIR/tests/cli/missing-features
  if [[ -d $mf ]]; then
    while IFS= read -r w; do
      flags=$(grep -m1 '^;; RUN:' "$w" | sed -n 's/.* -f \([^ ]*\).*/\1/p')
      convert "$w" "mf/$(basename "$w")" "$flags"
    done < <(find "$mf" -name '*.wast' | sort)
  fi
fi
wt_corpus_wasm | while IFS= read -r f; do
  printf '%s\t\n' "$f" >> "$cases"
done

echo "corpus: $(wc -l < "$cases") binaries" >&2

# One binary: every invocation, both tools.
run_case() {
  local f=$1 flags=$2 kind inv
  kind=module
  if [[ $(head -c 8 "$f" | od -An -tx1 | tr -d ' \n') == 0061736d0d000100 ]]; then kind=component; fi
  local -a invs=("validate" "objdump" "strip" "strip -a")
  if [[ $SWEEP -eq 1 ]]; then
    invs=("validate -f wasm1" "validate -f wasm2" "validate -f wasm3" "validate -f lime1"
      "validate -f mvp" "validate -f all" "validate -f -all")
  fi
  if [[ -n $flags ]]; then invs=("validate -f $flags"); fi
  for inv in "${invs[@]}"; do
    local uo ue oo oe us os verdict
    uo=$(mktemp); oo=$(mktemp)
    # shellcheck disable=SC2086
    set +e
    "$WT_UPSTREAM" $inv "$f" > "$uo" 2>/dev/null; us=$?
    "$ours" $inv "$f" > "$oo" 2>/dev/null; os=$?
    set -e
    if [[ $us -eq 0 && $os -eq 0 ]]; then
      if cmp -s "$uo" "$oo"; then verdict=agree; else verdict=stdout-differs; fi
    elif [[ $us -ne 0 && $os -ne 0 ]]; then verdict=agree
    elif [[ $us -eq 0 ]]; then verdict=ours-rejects
    else verdict=ours-accepts
    fi
    rm -f "$uo" "$oo"
    local name=$f
    case $f in
      "$OUT"/corpus/*) name=${f#"$OUT"/corpus/} ;;
      "$REPO"/*) name=repo/${f#"$REPO"/} ;;
    "$SIL_TOOLS"/*) name=pins/${f#"$SIL_TOOLS"/} ;;
      "$SIL_TOOLS"/*) name=pins/${f#"$SIL_TOOLS"/} ;;
    esac
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$kind" "$name" "$inv" "$us" "$os" "$verdict"
  done
}
export -f run_case
SWEEP=$sweep
OUT=$out
REPO=$repo
export WT_UPSTREAM ours SWEEP OUT REPO SIL_TOOLS

results=$out/results.tsv
tr '\t' '\n' < "$cases" | paste - - | \
  xargs -P "$jobs" -d '\n' -n 1 bash -c 'IFS=$'"'"'\t'"'"' read -r f fl <<< "$1"; run_case "$f" "$fl"' _ \
  > "$results"

echo "results: $results" >&2
awk -F'\t' '{ split($3, a, " "); key = $1 "\t" a[1] ($3 ~ / -a$/ ? " -a" : "") ($3 ~ / -f/ ? " -f " a[3] : "");
  n[key]++; v[key "\t" $6]++ }
  END { for (k in n) { printf "%s\t%d", k, n[k];
    split("agree ours-rejects ours-accepts stdout-differs", vs, " ");
    for (i = 1; i <= 4; i++) printf "\t%s=%d", vs[i], v[k "\t" vs[i]] + 0; printf "\n" } }' \
  "$results" | sort

if [[ $baseline -eq 1 ]]; then
  # known-diffs.txt: one disagreement per line, "kind<TAB>file<TAB>invocation<TAB>verdict"
  # (files relative to the corpus directory, or repo/<path>); `#` starts a comment.
  known=$here/known-diffs.txt
  awk -F'\t' '$6 != "agree" { print $1 "\t" $2 "\t" $3 "\t" $6 }' "$results" | sort > "$out/diffs.txt"
  grep -v '^#' "$known" 2>/dev/null | sort > "$out/known.txt" || true
  new=$(comm -23 "$out/diffs.txt" "$out/known.txt")
  cut -f2,3 "$results" | sort -u > "$out/ran.txt"
  fixed=$(comm -13 "$out/diffs.txt" "$out/known.txt" | \
    awk -F'\t' 'NR == FNR { ran[$1 "\t" $2] = 1; next } ($2 "\t" $3) in ran' "$out/ran.txt" -)
  if [[ -n $fixed ]]; then
    echo "known disagreements that now agree (remove them from $known):" >&2
    echo "$fixed" >&2
  fi
  if [[ -n $new ]]; then
    echo "disagreements not in $known:" >&2
    echo "$new" >&2
    exit 1
  fi
  echo "no disagreement outside $known" >&2
fi
exit 0
