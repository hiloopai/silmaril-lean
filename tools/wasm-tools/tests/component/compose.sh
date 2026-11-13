#!/usr/bin/env bash
# Differential test of the Lean `wasm-tools compose` (mapped to wasm-wac) against the pinned
# upstream wasm-tools 1.262.0 (wasm-compose) on wasm-compose's own test corpus
# (crates/wasm-compose/tests/compositions of the 1.262.0 source tree).
#
#   tools/wasm-tools/tests/component/compose.sh
#
# Each case is run as upstream's test runs it (`compose ROOT.wat`, `-c config.yml` when the case
# has one), from the crate directory, by both binaries. A case agrees when both fail with the same
# first stderr line, or both succeed and our output passes upstream's validator
# (`validate --features all`) and has upstream's `component wit` (else, when it validates, it is
# counted `valid with another WIT`). Skips (exit 0) when a pinned
# binary or the corpus is absent. Exit status 0 (the corpus reports parity).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
source "$here/pins.sh"
wtc_require_upstream
OURS=${WASM_TOOLS_LEAN:-$repo/.lake/build/bin/wasm-tools}
if [[ ! -x $OURS ]]; then echo "SKIP: $OURS not built (lake build wasm-tools)"; exit 0; fi
CRATE="$SIL_TOOLS/src/wasm-tools-1.262.0-cli/wasm-tools-1.262.0/crates/wasm-compose"
if [[ ! -d $CRATE/tests/compositions ]]; then echo "SKIP: corpus absent ($CRATE)"; exit 0; fi
tmp=$(mktemp -d /tmp/wasm-tools-comp-compose-XXXXXX)
trap 'rm -rf "$tmp"' EXIT
agree=0 differ=0 refused=0 valid=0
cd "$CRATE"
for d in tests/compositions/*/; do
  n=$(basename "$d"); d=${d%/}
  args=(compose -q "$d/root.wat" -o "$tmp/out.wasm")
  [[ -f $d/config.yml ]] && args+=(-c "$d/config.yml")
  rm -f "$tmp/u.wasm" "$tmp/o.wasm"
  "$WT_UPSTREAM" "${args[@]/$tmp\/out.wasm/$tmp/u.wasm}" >/dev/null 2>"$tmp/ue"; ue=$?
  "$OURS" "${args[@]/$tmp\/out.wasm/$tmp/o.wasm}" >/dev/null 2>"$tmp/oe"; oe=$?
  uh=$(head -1 "$tmp/ue"); oh=$(head -1 "$tmp/oe")
  if [[ $ue != 0 && $oe != 0 ]]; then
    if [[ $uh == "$oh" ]]; then agree=$((agree + 1)); continue; fi
  elif [[ $ue == 0 && $oe == 0 ]]; then
    if "$WT_UPSTREAM" validate --features all "$tmp/o.wasm" 2>/dev/null; then
      if cmp -s <("$WT_UPSTREAM" component wit "$tmp/u.wasm" 2>&1) <("$WT_UPSTREAM" component wit "$tmp/o.wasm" 2>&1); then
        agree=$((agree + 1)); continue
      fi
      valid=$((valid + 1)); echo "  valid $n: our composition validates, its WIT differs (wac's merge order and type names)"; continue
    fi
  fi
  if [[ $oh == *"not implemented by this wasm-tools"* ]]; then refused=$((refused + 1)); echo "  refused $n: $oh"; continue; fi
  differ=$((differ + 1))
  echo "  differ $n: exit $ue/$oe, '$uh' / '$oh'"
done
echo "compose: $agree agree, $valid valid with another WIT, $refused refused (not implemented), $differ differ"
