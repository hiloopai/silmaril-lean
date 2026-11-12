#!/usr/bin/env bash
# Run `cli-demo` (the demo grammar of Silmaril.Cli.Demo behind the derived front end) and check
# stdout, stderr and the exit code of each case against the expectations below, which are the
# texts the Lean examples in Silmaril/Cli/Demo/Thms.lean check by `#guard`.
#
#   tools/cli-demo/tests/run.sh [BINARY]
#
# BINARY defaults to $SIL_CLI_DEMO, else .lake/build/bin/cli-demo (built by
# `lake build cli-demo`). When it is absent the script skips (exit 0).
set -uo pipefail

root=$(cd "$(dirname "$0")/../../.." && pwd)
bin=${1:-${SIL_CLI_DEMO:-$root/.lake/build/bin/cli-demo}}
if [[ ! -x $bin ]]; then
  echo "skip: $bin not built (lake build cli-demo)"
  exit 0
fi

fail=0
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# check NAME EXPECTED_CODE EXPECTED_STDOUT EXPECTED_STDERR -- ARGS...
check() {
  local name=$1 code=$2 out=$3 err=$4
  shift 5
  "$bin" "$@" >"$tmp/out" 2>"$tmp/err"
  local got=$?
  local ok=1
  [[ $got == "$code" ]] || { echo "FAIL $name: exit $got, want $code"; ok=0; }
  [[ $(cat "$tmp/out") == "$out" ]] || { echo "FAIL $name: stdout"; diff <(echo "$out") "$tmp/out"; ok=0; }
  [[ $(cat "$tmp/err") == "$err" ]] || { echo "FAIL $name: stderr"; diff <(echo "$err") "$tmp/err"; ok=0; }
  if ((ok)); then echo "ok   $name"; else fail=1; fi
}

help_root='Instrument and run Wasm modules

Usage: demo [OPTIONS] <COMMAND>

Commands:
  asyncify  Run the verified pass
  run       Run an export

Options:
  -v, --verbose     Print more (repeat for more) [repeatable]
  -q, --quiet       Print less
  --color[=<WHEN>]  Colour output [possible values: auto, always, never]
  -V, --version     Print version
  -h, --help        Print help

Exit status:
  0  success
  1  the tool failed
  2  usage error'

help_asyncify='Run the verified pass

Usage: demo asyncify [OPTIONS] --output <PATH> <INPUT>

Arguments:
  <INPUT>  Input module

Options:
  -o, --output <PATH>  Output file [required]
  --pages <N>          Memory pages [default: 1]
  --[no-]selective     Instrument only suspending calls [repeatable]
  -O2                  Optimise first
  -q, --quiet          Print less
  -h, --help           Print help'

usage_tail='

Usage: demo [OPTIONS] <COMMAND>

For more information, try '"'"'--help'"'"'.'

usage_asyncify='

Usage: demo asyncify [OPTIONS] --output <PATH> <INPUT>

For more information, try '"'"'--help'"'"'.'

usage_run='

Usage: demo run [OPTIONS] <INPUT> <EXPORT> [ARGS]...

For more information, try '"'"'--help'"'"'.'

check help 0 "$help_root" "" -- --help
check help-short 0 "$help_root" "" -- -h
check help-sub 0 "$help_asyncify" "" -- asyncify --help
check help-sub-cluster 0 "$help_asyncify" "" -- asyncify -qh
check version 0 "demo 0.1.0" "" -- -V
check asyncify 0 'path: asyncify
input: in.wasm
output: out.wasm
pages: 1
verbose: flag' "" -- -v asyncify in.wasm -o out.wasm
check asyncify-normal-form 0 'path: asyncify
input: in.wasm
output: out.wasm
pages: 1
verbose: flag' "" -- --verbose asyncify --output out.wasm in.wasm
check attached-value 0 'path: asyncify
input: in.wasm
output: out.wasm
pages: 1
verbose: flag' "" -- -v asyncify -oout.wasm in.wasm
check clusters 0 'path: asyncify
input: in.wasm
output: out.wasm
pages: 1
verbose: flag, flag, flag
quiet: flag' "" -- -vvv asyncify in.wasm -qo out.wasm
check token-and-negation 0 'path: asyncify
input: a
output: b
pages: 1
selective: flag, off
O2: flag
color: flag' "" -- --color asyncify -O2 --selective --no-selective -o b a
check optional-value 0 'path: run
input: m
export: f
fuel: 1000000
side: src
color: never' "" -- --color=never run m f
check run-alias 0 'path: run
input: m.wasm
export: f
args: 1, 2
fuel: 1000000
side: src' "" -- r m.wasm f 1 2
DEMO_FUEL=7 check run-env 0 'path: run
input: m.wasm
export: f
args: 1, 2
fuel: 7
side: src' "" -- run m.wasm f 1 2
DEMO_FUEL=7 check run-cmdline-over-env 0 'path: run
input: m.wasm
export: f
fuel: 9
side: tgt' "" -- run --fuel=9 --side tgt m.wasm f
check dashdash 0 'path: run
input: m.wasm
export: -x
fuel: 1000000
side: src' "" -- run m.wasm -- -x
check missing-value 2 "" "error: a value is required for '-o' but none was supplied$usage_asyncify" -- asyncify in.wasm -o
check unknown-option 2 "" "error: unexpected argument '--nope' found$usage_tail" -- --nope
check unknown-in-cluster 2 "" "error: unexpected argument '-qx' found$usage_asyncify" -- asyncify -qx
check not-inherited 2 "" "error: unexpected argument '-v' found$usage_run" -- run -v m f
check flag-value 2 "" "error: unexpected value in '--no-selective=1': the flag takes no value$usage_asyncify" -- asyncify --no-selective=1
check unknown-command 2 "" "error: unrecognized subcommand 'frob'$usage_tail" -- frob
check missing-command 2 "" "error: 'demo' requires a subcommand but one was not provided$usage_tail" --
check bad-value 2 "" "error: invalid value 'x' for 'args': expected a natural number$usage_run" -- run m f x
check bad-enum 2 "" "error: invalid value 'both' for 'side': expected one of src, tgt$usage_run" -- run m f --side both
check bad-optional 2 "" "error: invalid value 'sometimes' for 'color': expected one of auto, always, never$usage_tail" -- --color=sometimes run m f
check missing-option 2 "" "error: the required option 'output' was not provided$usage_asyncify" -- asyncify a.wasm
check repeated 2 "" "error: the argument 'output' cannot be used multiple times$usage_asyncify" -- asyncify a -o b -o c

if ((fail)); then echo "cli-demo: FAILED"; exit 1; fi
echo "cli-demo: all cases passed"
