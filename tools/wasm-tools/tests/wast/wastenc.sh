#!/usr/bin/env bash
# Differential test of the `wast` crate encoder transcription (`Silmaril.Wasm.Tools.WastEnc`,
# driver `wasm-tools-wastenc`) against the pinned `wasm-tools parse` 1.262.0.
#
#   tools/wasm-tools/tests/wast/wastenc.sh [--bin PATH] [--jobs N] [--limit N] [--list OUT]
#
# Corpus: upstream's tests/snapshots/testsuite/**/*.print (2843 core modules printed by
# wasmprinter from the spec and proposal testsuites, the corpus of parse-print.sh). For every
# file upstream parses, ours `wasm-tools-wastenc F o.wasm` against upstream `parse F -o u.wasm`:
# `same` (byte-identical), `differ`, `rejected` (ours fails), `upstream_rejects`. One summary
# line; `--list OUT` writes `class<TAB>file` for every file. Skips (status 0) without the
# pinned binary or the source archive; the upstream binary is called by its absolute path.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
source "$here/pins.sh"
bin="$here/../../../.lake/build/bin/wasm-tools-wastenc"; limit=0; jobs=6; list=""
while [[ $# -gt 0 ]]; do
  case $1 in
    --bin) bin=$2; shift 2;; --limit) limit=$2; shift 2;; --jobs) jobs=$2; shift 2;;
    --list) list=$2; shift 2;;
    *) echo "usage: $0 [--bin PATH] [--jobs N] [--limit N] [--list OUT]"; exit 2;;
  esac
done
wt_require_upstream; wt_require_src
wt_require_ours "$bin" wasm-tools-wastenc
bin=$(cd "$(dirname "$bin")" && pwd)/$(basename "$bin")
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
root="$WT_SRC_DIR/tests/snapshots/testsuite"
mapfile -t files < <(cd "$root" && find . -name '*.print' | sed 's|^\./||' | sort)
[[ $limit -gt 0 ]] && files=("${files[@]:0:$limit}")
one() {
  local rel=$1 f="$root/$1" d; d=$(mktemp -d "$tmp/w.XXXXXX")
  if ! "$WT_UPSTREAM" parse "$f" -o "$d/u.wasm" 2>/dev/null; then
    printf 'upstream_rejects\t%s\n' "$rel"
  elif timeout 120 "$bin" "$f" "$d/o.wasm" 2>/dev/null; then
    if cmp -s "$d/o.wasm" "$d/u.wasm"; then printf 'same\t%s\n' "$rel"
    else printf 'differ\t%s\n' "$rel"; fi
  else printf 'rejected\t%s\n' "$rel"; fi
  rm -rf "$d"
}
export -f one; export root bin tmp WT_UPSTREAM
printf '%s\n' "${files[@]}" | xargs -P "$jobs" -I{} bash -c 'one "$@"' _ {} > "$tmp/res"
[[ -n $list ]] && sort -k2 "$tmp/res" > "$list"
c() { grep -c "^$1	" "$tmp/res" || true; }
echo "SUMMARY wastenc same=$(c same) differ=$(c differ) rejected=$(c rejected) upstream_rejects=$(c upstream_rejects) files=${#files[@]}"
