#!/usr/bin/env bash
# Compare wasm-asyncify, wasm-verify, wasm-jco and wasm-wac with their CLI
# specifications (Silmaril.Cli.Spec.{Asyncify,WasmVerify,Jco,Wac}: args grammars in the clap
# dialect) on the corpus `cli-spec corpus TOOL` derives from each.
#
#   tools/cli-spec/tests/pinned-tools.sh
#
# Needs .lake/build/bin/{cli-spec,wasm-asyncify,wasm-verify,wasm-jco,wasm-wac}
# (`lake build cli-spec wasm-asyncify wasm-verify wasm-jco wasm-wac`); skips a
# tool (exit 0)
# when a binary is missing. Every vector runs in an empty scratch directory with stdin from
# /dev/null; files named in the corpus do not exist. The tool's answer is classed as exit 0,
# a usage error (another exit code and `usage:` on stderr, any case) or a run (otherwise); the
# specification's as help or version (`0`: exit 0), a usage error, a run (which may exit 0), or
# either (`run|N`). The exact texts of help and usage errors are checked by
# `cli-harness front` (tools/cli-harness/tests/surfaces.sh). The vectors on which they differ must be
# exactly those of tools/cli-spec/tests/known-differences.tsv (tool, then the vector,
# tab-separated); `--update` rewrites that file.
#
# wasm-opt is compared inside Lean instead (Silmaril.Wasm.Binaryen.DriverSpec).
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/../../.." && pwd)
BIN=$ROOT/.lake/build/bin
KNOWN=$ROOT/tools/cli-spec/tests/known-differences.tsv
[[ -x $BIN/cli-spec ]] || { echo "SKIP: $BIN/cli-spec not built (lake build cli-spec)"; exit 0; }

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
: >"$work/found"
for tool in wasm-asyncify wasm-verify wasm-jco wasm-wac; do
  if [[ ! -x $BIN/$tool ]]; then echo "SKIP: $BIN/$tool not built"; continue; fi
  total=0; agree=0
  while IFS=$'\t' read -r -a line; do
    cls=${line[0]}; argv=("${line[@]:1}")
    total=$((total + 1))
    rm -rf "$work/cwd"; mkdir "$work/cwd"
    set +e
    (cd "$work/cwd" && timeout 20 "$BIN/$tool" "${argv[@]}" </dev/null >/dev/null 2>"$work/err")
    rc=$?
    set -e
    if [[ $rc == 0 ]]; then got=0
    elif grep -qi 'usage:' "$work/err"; then got=usage
    else got=run; fi
    case $cls in
      0) ok=0 ;;                               # help or version: exit 0
      run) ok="run 0" ;;                       # the program ran (and failed or succeeded)
      run\|*) ok="$got" ;;                     # left to the program
      *) ok=usage ;;                           # a usage error
    esac
    if [[ " $ok " == *" $got "* ]]; then agree=$((agree + 1))
    else printf '%s\t%s\n' "$tool" "$(IFS=$'\t'; echo "${argv[*]}")" >>"$work/found"; fi
  done < <("$BIN/cli-spec" corpus "$tool")
  echo "$tool: $agree/$total vectors read alike"
done
if [[ ${1:-} == --update ]]; then { head -2 "$KNOWN"; cat "$work/found"; } >"$work/new"; cp "$work/new" "$KNOWN"; echo "updated $KNOWN"; exit 0; fi
if diff <(grep -v '^#' "$KNOWN" | sort) <(sort "$work/found") >"$work/diff"; then
  echo "differences: exactly the $(grep -vc '^#' "$KNOWN") pinned in known-differences.tsv"
else
  echo "FAIL: differences changed (< pinned, > found):"; cat "$work/diff"; exit 1
fi
