#!/usr/bin/env bash
# The opt-in differential suites of wasm-tools against the pinned upstream 1.262.0 and its
# corpora (tools/wasm-tools/tests/fetch-pins.sh installs them): one line per suite, then a
# summary. Not part of the fast check (tools/wasm-tools/test-cli.py); run it on demand or
# nightly. Each suite skips (status 0) without its pins.
#
#   tools/wasm-tools/tests/differential.sh [--quick] [SUITE]...
#
# Suites: validate dump parse-print meta meta-malformed addr2line wast golden. `--quick` runs
# the repository-only or bounded variants. `golden` re-records the golden suites into a
# scratch copy and fails when any recorded outcome changed.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
# shellcheck source=pins.sh
source "$here/pins.sh"
quick=0
suites=()
for a in "$@"; do
  case $a in
    --quick) quick=1 ;;
    validate|dump|parse-print|meta|meta-malformed|addr2line|wast|golden) suites+=("$a") ;;
    *) echo "usage: differential.sh [--quick] [SUITE]..." >&2; exit 2 ;;
  esac
done
[[ ${#suites[@]} -gt 0 ]] || suites=(golden validate dump parse-print meta meta-malformed addr2line wast)
wt_require_upstream
q() { [[ $quick == 1 ]] && printf '%s\n' "$@"; }

golden() {
  local tmp rc=0; tmp=$(mktemp -d)
  mkdir "$tmp/wasm-tools"
  cp -r "$here/../test-cli.py" "$tmp/wasm-tools/" && cp -r "$here" "$tmp/wasm-tools/tests"
  if ! python3 -I "$tmp/wasm-tools/tests/golden-capture.py" "$WT_UPSTREAM" >/dev/null; then
    echo "golden: capture failed"; rc=1
  elif ! diff -r "$here/golden" "$tmp/wasm-tools/tests/golden" > "$tmp/golden.diff"; then
    echo "golden: recorded outcomes changed:"; head -40 "$tmp/golden.diff"; rc=1
  else echo "golden: every recorded outcome reproduced"; fi
  rm -rf "$tmp"; return $rc
}
run_suite() {
  case $1 in
    golden) golden ;;
    validate) bash "$here/diff.sh" $(q --quick) ;;
    dump) bash "$here/dump-diff.sh" $(q --quick) ;;
    parse-print) bash "$here/parse-print.sh" $(q --limit 200) ;;
    meta) bash "$here/meta-differential.sh" ;;
    meta-malformed) bash "$here/meta-malformed.sh" $(q -n 100) ;;
    addr2line) bash "$here/addr2line/differential.sh" ;;
    wast)
      if [[ -d $WASM_SPEC_DIR ]]; then bash "$here/wast/differential.sh" "$WASM_SPEC_DIR"
      else echo "SKIP: $WASM_SPEC_DIR absent (fetch-pins.sh spec)"; fi ;;
  esac
}
fail=0
summary=()
for s in "${suites[@]}"; do
  log=$(mktemp)
  run_suite "$s" > "$log" 2>&1; rc=$?
  last=$(grep -v '^\s*$' "$log" | tail -1)
  if [[ $rc == 0 ]]; then summary+=("ok    $s: $last"); else summary+=("FAIL  $s: $last"); fail=1; cat "$log"; fi
  rm -f "$log"
done
printf '%s\n' "${summary[@]}"
exit $fail
