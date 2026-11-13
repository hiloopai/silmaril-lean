#!/usr/bin/env bash
# Argument handling of `validate`, `print`, `parse`: our Lean binary against the pinned
# upstream wasm-tools 1.262.0, invocation by invocation.
#
#   tools/wasm-tools/tests/compval/args.sh
#
# Each invocation (below) runs in a scratch directory holding `c.wasm` (a small component) and
# `c.wat` (its text), with stdin from /dev/null, against both binaries; the exit status must be
# equal, and stdout and stderr byte-identical, except for lines listed as known differences
# (`error:` messages of validation failures, whose class only is compared; with `-v`, upstream's
# log lines on stderr, which this binary does not write). Prints one line per
# invocation and a summary; exit 1 on a difference, 77 when a pinned tool or the binary is absent.

set -uo pipefail
root=$(cd "$(dirname "$0")/../../../.." && pwd)
# shellcheck source=../../../wasm-jco/tests/pins.sh
source "$root/tools/wasm-jco/tests/pins.sh"
wt=$WASM_TOOLS
ours=${WASM_TOOLS_LEAN:-$root/.lake/build/bin/wasm-tools-cv}
if [[ ! -x $wt || $(sha256sum "$wt" | cut -d' ' -f1) != "$WASM_TOOLS_SHA256" ]]; then
  echo "compval/args: SKIP: pinned wasm-tools $WASM_TOOLS_VERSION not found at $wt" >&2
  exit 77
fi
[[ -x $ours ]] || { echo "compval/args: SKIP: $ours missing" >&2; exit 77; }

d=$(mktemp -d /tmp/compval-args.XXXXXX)
trap 'rm -rf "$d"' EXIT
cp "$root/tests/wat/fixtures/demo.wasm" "$d/c.wasm"
printf '(component (core module binary "\\00asm\\01\\00\\00\\00") (import "f" (func)))\n' > "$d/bad.wat"
printf '(component (import "a" (func)))\n' > "$d/c.wat"
cd "$d" || exit 1

# One invocation per line; `|` separates arguments (so that empty and spaced ones survive).
cases=(
  "validate|c.wasm" "validate|-f|all|c.wasm" "validate|--features=all|c.wasm"
  "validate|-fall|c.wasm" "validate|-f=all|c.wasm" "validate|-f|all,-cm-async|c.wasm"
  "validate|--features|-all|c.wasm" "validate|--features|wasm1|c.wasm"
  "validate|--features|nope|c.wasm" "validate|--features|-wasm2|c.wasm" "validate|-f"
  "validate|--features" "validate|--foo" "validate|-x" "validate|c.wasm|d.wasm"
  "validate|--validate-custom=x|c.wasm" "validate|--color|never|--color|never|c.wasm"
  "validate|--color|bad|c.wasm" "validate|-g|--generate-dwarf|lines|c.wasm"
  "validate|--generate-dwarf|bogus|c.wasm" "validate|-vv|c.wasm" "validate|-v|-v|c.wasm"
  "validate|/nonexistent.wasm" "validate|--|c.wasm" "validate|--|-x" "validate|c.wat"
  "validate|-h" "validate|--help" "print|-h" "print|--help" "parse|-h" "parse|--help"
  "print|c.wasm" "print|c.wasm|-o" "print|c.wasm|-o|x.wat|-o|y.wat" "print|--indent|"
  "parse|c.wat" "parse|-t|c.wat" "parse|--wat|c.wat" "print|/nonexistent.wasm"
  "parse|c.wasm|-t" "validate|--features|-v|c.wasm" "print|-o|--skeleton|c.wasm" "validate|-f|--nope|c.wasm" "validate|-xyz"
)

pass=0 fail=0
for c in "${cases[@]}"; do
  IFS='|' read -r -a args <<< "$c"
  "$wt" "${args[@]}" < /dev/null > up.out 2> up.err; ur=$?
  "$ours" "${args[@]}" < /dev/null > us.out 2> us.err; orc=$?
  why=
  [[ $ur == "$orc" ]] || why="exit $ur vs $orc"
  # known difference: `-v` turns on upstream's `env_logger` lines (timestamps) on stderr
  verbose=0; for a in "${args[@]}"; do [[ $a == -v* || $a == --verbose ]] && verbose=1; done
  if [[ -z $why && $verbose == 0 ]] && ! cmp -s up.err us.err; then
    # validation and parse failures: compare the class (an `error:` line), not the text
    if [[ $ur == 1 ]] && grep -q '^error: ' up.err && grep -q '^error: ' us.err; then :; else why="stderr differs"; fi
  fi
  if [[ -z $why ]] && ! cmp -s up.out us.out; then
    case ${args[0]} in
      print|parse) [[ $ur == 0 ]] || why="stdout differs" ;;  # printed text: see print-parse.sh
      *) why="stdout differs" ;;
    esac
  fi
  if [[ -z $why ]]; then pass=$((pass + 1)); echo "ok   ${args[*]}"
  else fail=$((fail + 1)); echo "DIFF ${args[*]}: $why"; fi
done
echo "args: $pass passed, $fail differ"
[[ $fail == 0 ]]
