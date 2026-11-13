#!/usr/bin/env bash
# Differential run of upstream's `tests/cli` directives for the `component` subcommands.
#
#   tools/wasm-tools/tests/component/cli-corpus.sh [-v] [FILTER]
#
# Reads every `// RUN[...]:` / `// FAIL[...]:` directive (with `\` continuations, `|` pipes and
# `%` for the test file, as upstream's `tests/cli.rs` reads them) of the files in
# `tests/cli/` of the pinned wasm-tools 1.262.0 source tree whose first command is
# `component …` (optionally only those whose command contains FILTER), runs it once with the
# pinned upstream binary (absolute path) and once with the Lean binary in every position of the
# pipeline, and compares stdout (bytes), the first stderr line and the exit status. Each
# directive is classified `agree` (all three), `stdout+exit` (stdout and status agree, the first
# stderr line differs: upstream's messages carry byte offsets and wasmparser texts) or `differ`.
# Skips (exit 0) when the pinned binary, the Lean binary or the source tree is absent. Exit
# status 0 always (the corpus reports parity; see docs/projects/wasm-components.md).
#
# Every stage of a pipeline runs under `timeout` (CLI_CORPUS_TIMEOUT seconds, default 60): a
# stage that does not finish is killed, its status is 124 and the directive is reported as
# `differ ... timeout`; the count of such directives is printed at the end.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
source "$here/pins.sh"
wtc_require_upstream
OURS=${WASM_TOOLS_LEAN:-$repo/.lake/build/bin/wasm-tools}
if [[ ! -x $OURS ]]; then echo "SKIP: $OURS not built (lake build wasm-tools)"; exit 0; fi
SRC="$SIL_TOOLS/src/wasm-tools-1.262.0-cli/wasm-tools-1.262.0/tests/cli"
if [[ ! -d $SRC ]]; then echo "SKIP: upstream source tree absent ($SRC)"; exit 0; fi
verbose=0
if [[ ${1:-} == -v ]]; then verbose=1; shift; fi
filter=${1:-}
limit=${CLI_CORPUS_TIMEOUT:-60}
command -v timeout >/dev/null || { echo "FAIL: needs timeout (coreutils)"; exit 1; }
tmp=$(mktemp -d /tmp/wasm-tools-comp-cli-corpus-XXXXXX)
trap 'rm -rf "$tmp"' EXIT

# directives FILE: one line per directive, `name US fail US command` (US: the unit separator, 0x1f)
directives() {
  awk '
    function flush() { if (have) { printf "%s\037%s\037%s\n", name, fail, cmd }; have = 0 }
    {
      l = $0
      if (l == "") next
      if (substr(l, 1, 3) == "// ") l = substr(l, 4)
      else if (substr(l, 1, 3) == ";; ") l = substr(l, 4)
      else next
      if (cont) { cmd = cmd l; if (cmd ~ /\\$/) { sub(/\\$/, "", cmd) } else { cont = 0; flush() } ; next }
      if (l ~ /^RUN/) { fail = 0; d = substr(l, 4) } else if (l ~ /^FAIL/) { fail = 1; d = substr(l, 5) } else next
      if (substr(d, 1, 1) == "[") { i = index(d, "]:"); name = substr(d, 2, i - 2); cmd = substr(d, i + 2) }
      else if (substr(d, 1, 1) == ":") { name = ""; cmd = substr(d, 2) } else next
      have = 1
      if (cmd ~ /\\$/) { sub(/\\$/, "", cmd); cont = 1 } else flush()
    }' "$1"
}

# run BIN FILE CMD > stdout, stderr in $3.err; prints the exit status of the last stage
run_pipeline() {
  local bin=$1 file=$2 cmd=$3 out=$4
  local -a stages=() cur=()
  local a input="$tmp/empty" st=0 k=0
  : > "$tmp/empty"
  for a in $cmd; do
    if [[ $a == "|" ]]; then stages+=("${cur[*]}"); cur=(); continue; fi
    [[ $a == "%" ]] && a=$file
    a=${a//%tmpdir/$tmp/td}
    cur+=("$a")
  done
  stages+=("${cur[*]}")
  mkdir -p "$tmp/td"
  for s in "${stages[@]}"; do
    k=$((k + 1))
    # shellcheck disable=SC2086
    (cd "$tmp/td" && env WAST_STRICT_COMPONENT_INDICES=1 COLUMNS=80 timeout -k 5 "$limit" "$bin" $s <"$input" >"$out.$k" 2>"$out.err")
    st=$?
    input="$out.$k"
  done
  cp "$out.$k" "$out"
  echo "$st"
}

agree=0 soft=0 differ=0 timeouts=0
for f in "$SRC"/*.wit "$SRC"/*.wat "$SRC"/*.wast; do
  [[ -f $f ]] || continue
  while IFS=$'\037' read -r name fail cmd; do
    first=$(echo "$cmd" | awk '{print $1}')
    [[ $first == component ]] || continue
    [[ -z $filter || $cmd == *"$filter"* ]] || continue
    id="$(basename "$f")${name:+[$name]}"
    rm -rf "$tmp/td"
    ue=$(run_pipeline "$WT_UPSTREAM" "$f" "$cmd" "$tmp/u")
    rm -rf "$tmp/td"
    oe=$(run_pipeline "$OURS" "$f" "$cmd" "$tmp/o")
    uh=$(head -1 "$tmp/u.err"); oh=$(head -1 "$tmp/o.err")
    if [[ $ue == "$oe" ]] && cmp -s "$tmp/u" "$tmp/o"; then
      if [[ $uh == "$oh" ]]; then agree=$((agree + 1))
      else soft=$((soft + 1)); [[ $verbose == 1 ]] && echo "  stderr $id: '$uh' / '$oh'"; fi
    else
      differ=$((differ + 1))
      to=""
      if [[ $ue == 124 || $oe == 124 ]]; then timeouts=$((timeouts + 1)); to=" timeout (${limit}s)"; fi
      echo "  differ $id [$cmd] exit $ue/$oe$(cmp -s "$tmp/u" "$tmp/o" || echo ', stdout differs')$to: '$oh'"
    fi
  done < <(directives "$f")
done
echo "cli-corpus: $agree agree, $soft stdout+exit, $differ differ ($timeouts timed out after ${limit}s)"
