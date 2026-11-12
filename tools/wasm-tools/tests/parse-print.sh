#!/usr/bin/env bash
# Differential test of `wasm-tools parse` / `print` against the pinned upstream 1.262.0.
#
#   tools/wasm-tools/tests/parse-print.sh [--bin PATH] [--jobs N] [--limit N] [--out DIR]
#                                         [--print-flags "FLAGS;FLAGS;…"] [--check]
#
# Corpus: upstream's tests/snapshots/testsuite/**/*.print (WAT printed by wasmprinter from the
# spec and proposal testsuites; 2843 files). For each file F that upstream parses (u.wasm):
#   parse:   ours `parse F -o o.wasm` vs upstream `parse F -o u.wasm`: exit status, bytes
#   print:   ours `print u.wasm` vs upstream `print u.wasm`: exit status and text, once with no
#            flags and once per entry of --print-flags (default: -p, --skeleton,
#            --name-unnamed, "--indent 6", "--indent-text ab", "-p --skeleton --indent 3",
#            -f, "-f -p", "-f --name-unnamed --indent 3")
#   cert:    `print u.wasm` with WASM_TOOLS_LEAN_PRINT_CHECK=1: whether the printed text passed the
#            certified check (`Silmaril.Wasm.Tools.Print.check`)
# Reports per class: same / differ / rejected. The 126 files that use proposals outside
# silmaril-lean's Wasm 3.0 model (custom descriptors, compact imports, custom page sizes,
# threads, wide arithmetic) are rejected by our decoder and elaborator; they are listed in
# known-pp-rejects.txt.
#
# --check: regression test; fails (status 1) when a file outside known-pp-rejects.txt is
# rejected, when a print or parse result differs, or when a printed output is not certified. Skips (status 0) without the pinned binary or the source archive.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/pins.sh"
bin="$here/../../../.lake/build/bin/wasm-tools"; limit=0; out=""; jobs=6; check=0
pflags='-p;--skeleton;--name-unnamed;--indent 6;--indent-text ab;-p --skeleton --indent 3;-f;-f -p;-f --name-unnamed --indent 3'
while [[ $# -gt 0 ]]; do
  case $1 in
    --bin) bin=$2; shift 2;; --limit) limit=$2; shift 2;; --out) out=$2; shift 2;;
    --jobs) jobs=$2; shift 2;; --print-flags) pflags=$2; shift 2;; --check) check=1; shift;;
    *) echo "usage: $0 [--bin PATH] [--jobs N] [--limit N] [--out DIR] [--print-flags S] [--check]"; exit 2;;
  esac
done
wt_require_upstream; wt_require_src
wt_require_ours "$bin" wasm-tools
bin=$(cd "$(dirname "$bin")" && pwd)/$(basename "$bin")
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
[[ -n $out ]] && mkdir -p "$out"
root="$WT_SRC_DIR/tests/snapshots/testsuite"
mapfile -t files < <(cd "$root" && find . -name '*.print' | sed 's|^\./||' | sort)
[[ $limit -gt 0 ]] && files=("${files[@]:0:$limit}")
printf '%s\n' "${files[@]}" > "$tmp/list"

# One file: prints `class<TAB>file` lines.
one() {
  local rel=$1 f="$root/$1" d; d=$(mktemp -d "$tmp/w.XXXXXX")
  if ! "$WT_UPSTREAM" parse "$f" -o "$d/u.wasm" 2>/dev/null; then
    printf 'upstream_rejects\t%s\n' "$rel"; rm -rf "$d"; return; fi
  if "$bin" parse "$f" -o "$d/o.wasm" 2>/dev/null; then
    if cmp -s "$d/o.wasm" "$d/u.wasm"; then printf 'parse_same\t%s\n' "$rel"
    else printf 'parse_differ\t%s\n' "$rel"; fi
  else printf 'parse_rejected\t%s\n' "$rel"; fi
  local fl cls us os fa entries
  IFS=';' read -r -a entries <<< ";$pflags"
  for fl in "${entries[@]}"; do
    cls="print"; [[ -n $fl ]] && cls="print[$fl]"
    read -r -a fa <<< "$fl"
    "$WT_UPSTREAM" print "${fa[@]}" "$d/u.wasm" > "$d/u.wat" 2>/dev/null; us=$?
    "$bin" print "${fa[@]}" "$d/u.wasm" > "$d/o.wat" 2>/dev/null; os=$?
    if [[ $os -ne 0 && $us -eq 0 ]]; then printf '%s_rejected\t%s\n' "$cls" "$rel"
    elif [[ $os -eq $us ]] && cmp -s "$d/o.wat" "$d/u.wat"; then printf '%s_same\t%s\n' "$cls" "$rel"
    else printf '%s_differ\t%s\n' "$cls" "$rel"; fi
  done
  if WASM_TOOLS_LEAN_PRINT_CHECK=1 "$bin" print "$d/u.wasm" 2>&1 >/dev/null | grep -q 'print-check: certified'; then
    printf 'cert_certified\t%s\n' "$rel"
  elif "$bin" print "$d/u.wasm" >/dev/null 2>&1; then printf 'cert_uncertified\t%s\n' "$rel"; fi
  rm -rf "$d"
}
export -f one; export root bin tmp pflags WT_UPSTREAM
t0=$(date +%s)
xargs -a "$tmp/list" -P "$jobs" -I{} bash -c 'one "$@"' _ {} > "$tmp/res"
t1=$(date +%s)
cut -f1 "$tmp/res" | sort | uniq -c | sed -E 's/^ *([0-9]+) (.*)$/\2\t\1/' | awk -F'\t' '{printf "%-44s %s\n", $1, $2}'
echo "files ${#files[@]}, $((t1 - t0)) s with $jobs jobs"
[[ -n $out ]] && cp "$tmp/res" "$out/results.tsv"
if [[ $check == 1 ]]; then
  known="$here/known-pp-rejects.txt"; fail=0
  bad=$(awk -F'\t' '$1 ~ /_rejected$/ {print $2}' "$tmp/res" | sort -u | comm -23 - <(grep -v '^#' "$known" | sort -u))
  [[ -n $bad ]] && { echo "FAIL: rejected outside known-pp-rejects.txt:"; echo "$bad" | head; fail=1; }
  n=$(grep -c $'^print[^\t]*_differ\t' "$tmp/res"); [[ $n -gt 0 ]] && { echo "FAIL: $n print results differ"; fail=1; }
  n=$(grep -c $'^cert_uncertified\t' "$tmp/res"); [[ $n -gt 0 ]] && { echo "FAIL: $n printed outputs uncertified"; fail=1; }
  n=$(grep -c $'^parse_differ\t' "$tmp/res"); [[ $n -gt 0 ]] && { echo "FAIL: $n parse results differ"; fail=1; }
  [[ $fail == 0 ]] && echo "parse-print: check passed"
  exit $fail
fi
