#!/usr/bin/env bash
# Check the pinned CLI specification `Silmaril.Cli.Spec.WasmTools` against wasm-tools 1.262.0.
#
#   tools/cli-spec/tests/wasm-tools-surface.sh
#
# Needs `.lake/build/bin/cli-spec` (`lake build cli-spec`) and the pinned binary
# ~/.cache/silmaril-tools/wasm-tools-1.262.0/wasm-tools (SHA-256 below; tools/wasm-tools/README.md).
# Skips with a message (exit 0) when either is missing, so CI is unaffected.
#
# 1. help: for every command path, `cli-spec show wasm-tools PATH` (the help derived from
#    the grammar, in clap's layout) equals `wasm-tools PATH -h` modulo whitespace, and
#    `cli-spec text wasm-tools [-l] PATH` (the same rendered exactly, with wrapping and the long
#    texts of `Silmaril.Cli.Spec.WasmTools.Doc`) equals `wasm-tools PATH -h` / `--help` byte for
#    byte, at 100 columns (COLUMNS unset) and with `-w 80` / COLUMNS=80.
# 2. reading: for every argument vector of `cli-spec corpus wasm-tools`, the exit class of
#    the reading `Clap.Tool.read` (args grammar, clap dialect, value checks and rules) agrees
#    with the binary run on it (in an empty scratch directory, stdin from /dev/null):
#    help/version 0 <-> exit 0, usage error 2 <-> a clap usage error (exit 2 with clap's
#    "For more information, try '--help'." or a help text on stderr), "run" <-> anything else,
#    "run|2" (a value the specification leaves to the program, e.g. a file clap's value parser
#    reads) <-> either. A "run" that upstream rejects with `invalid value` is counted as a
#    value-type rejection, one rejected with "required arguments were not provided" or "cannot
#    be used with" as a requires/conflicts rule: both are modelled now, so both counts should
#    be 0 (before value types and rules were modelled: 48 and 2).
# 3. messages (informational, does not fail): for every vector the reading refuses
#    (`cli-spec errors wasm-tools`), whether the first line of its message equals the first
#    line of upstream's stderr, or is a prefix of it (clap appends reasons and tips).
# 4. texts: the whole output of the front end on the outcomes that do not run, byte for byte
#    (see below).
set -euo pipefail

WT=${WASM_TOOLS:-$HOME/.cache/silmaril-tools/wasm-tools-1.262.0/wasm-tools}
WT_SHA=fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211
ROOT=$(cd "$(dirname "$0")/../../.." && pwd)
CS=$ROOT/.lake/build/bin/cli-spec

if [[ ! -x $WT ]]; then echo "SKIP: pinned wasm-tools 1.262.0 not found at $WT"; exit 0; fi
if [[ ! -x $CS ]]; then echo "SKIP: $CS not built (lake build cli-spec)"; exit 0; fi
got=$(sha256sum "$WT" | cut -d' ' -f1)
if [[ $got != "$WT_SHA" ]]; then echo "FAIL: $WT has SHA-256 $got, want $WT_SHA"; exit 1; fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir "$work/cwd"
norm() { tr -s ' \n\t' '   ' | sed 's/^ //; s/ $//'; }

fail=0
# 1. help
paths=0; helpok=0; exact=0
while IFS= read -r p; do
  paths=$((paths + 1))
  read -r -a pa <<<"$p"
  "$CS" show wasm-tools "${pa[@]}" | norm >"$work/lean"
  (cd "$work/cwd" && "$WT" "${pa[@]}" -h) | norm >"$work/up"
  if cmp -s "$work/lean" "$work/up"; then helpok=$((helpok + 1))
  else echo "HELP MISMATCH: wasm-tools $p"; diff <(fold -w 100 "$work/lean") <(fold -w 100 "$work/up") | head -8; fail=1; fi
  # the same in clap's exact layout, -h and --help, byte for byte, at 100 columns (COLUMNS
  # unset) and at COLUMNS=80 (upstream's own CLI tests)
  for mode in short long short80 long80; do
    case $mode in
      short) flag=-h; lflag=() ;;
      long) flag=--help; lflag=(-l) ;;
      short80) flag=-h; lflag=(-w 80) ;;
      long80) flag=--help; lflag=(-l -w 80) ;;
    esac
    "$CS" text wasm-tools "${lflag[@]}" "${pa[@]}" >"$work/lean"
    if [[ $mode == *80 ]]; then
      (cd "$work/cwd" && env -u LINES COLUMNS=80 "$WT" "${pa[@]}" "$flag") >"$work/up"
    else
      (cd "$work/cwd" && env -u COLUMNS -u LINES "$WT" "${pa[@]}" "$flag") >"$work/up"
    fi
    if cmp -s "$work/lean" "$work/up"; then exact=$((exact + 1))
    else echo "EXACT HELP MISMATCH: wasm-tools $p $flag ($mode)"; diff "$work/lean" "$work/up" | head -8; fail=1; fi
  done
done < <("$CS" paths wasm-tools)
echo "help: $helpok/$paths command paths equal modulo whitespace"
echo "help: $exact/$((4 * paths)) texts (-h and --help of every path, 100 and 80 columns) byte-identical"

# 2. reading
total=0; agree=0; typed=0; rel=0; bad=0; und=0; undu=0
while IFS=$'\t' read -r -a line; do
  cls=${line[0]}; argv=("${line[@]:1}")
  total=$((total + 1))
  set +e
  (cd "$work/cwd" && timeout 20 "$WT" "${argv[@]}" </dev/null >/dev/null 2>"$work/err")
  rc=$?
  set -e
  ok=0
  usage=0
  if [[ $rc == 2 ]] && { grep -q "For more information, try '--help'." "$work/err" ||
                         grep -q '^Usage: ' "$work/err"; }; then usage=1; fi
  case $cls in
    0) [[ $rc == 0 ]] && ok=1 ;;
    2) [[ $usage == 1 ]] && ok=1 ;;
    run\|2) ok=1; und=$((und + 1)); if [[ $usage == 1 ]]; then undu=$((undu + 1)); fi ;;
    run) if [[ $usage == 0 ]]; then ok=1
         elif grep -q "invalid value" "$work/err"; then ok=2
         elif grep -qE "required arguments were not provided|cannot be used with" "$work/err"; then ok=3; fi ;;
  esac
  if [[ $ok == 1 ]]; then agree=$((agree + 1))
  elif [[ $ok == 2 ]]; then typed=$((typed + 1))
  elif [[ $ok == 3 ]]; then rel=$((rel + 1))
  else
    bad=$((bad + 1)); fail=1
    echo "READING MISMATCH: spec $cls, wasm-tools exit $rc: ${argv[*]}"
    head -c 300 "$work/err" | head -3
  fi
done < <("$CS" corpus wasm-tools)
echo "reading: $agree/$total agree, $typed value-type rejections and $rel requires/conflicts rejections not modelled, $bad mismatches"
echo "left to the program (run|2): $und, of which upstream refused $undu"
[[ $typed == 0 && $rel == 0 ]] || fail=1
rm -rf "$work/cwd"; mkdir "$work/cwd"

# 3. messages
mtotal=0; mexact=0; mprefix=0
while IFS=$'\t' read -r -a line; do
  msg=${line[0]}; argv=("${line[@]:1}")
  mtotal=$((mtotal + 1))
  set +e
  up=$(cd "$work/cwd" && timeout 20 "$WT" "${argv[@]}" </dev/null 2>&1 >/dev/null | head -1)
  set -e
  if [[ $up == "$msg" ]]; then mexact=$((mexact + 1))
  elif [[ $up == "$msg"* ]]; then mprefix=$((mprefix + 1))
  elif [[ -n ${SHOW_MESSAGES:-} ]]; then printf 'MESSAGE: %s\n   ours: %s\n   upstream: %s\n' "${argv[*]}" "$msg" "$up"; fi
done < <("$CS" errors wasm-tools)
echo "messages: $mexact/$mtotal first lines equal upstream's, $mprefix more are a prefix of it"

# 4. texts: on every corpus vector that does not run, and on the vectors of
#    wasm-tools-texts.argv (one per line, split at spaces), what the front end prints
#    (`cli-spec run`: Clap.Tool.text, i.e. clap's exact texts of Silmaril.Cli.Clap.Exact) equals
#    upstream's stdout, stderr and exit code byte for byte. Known differences of the reading
#    itself (not of the texts) are listed in `known`.
known=$'metadata add --licenses 1 --licenses 1\ncompletion -- -t bash'
ttotal=0; texact=0; tknown=0
# 5. the binary: the same texts printed by the full build of `wasm-tools`, whose `main` is
#    `Clap.Tool.main` over this specification (`tools/wasm-tools/WasmTools/SpecMain.lean`);
#    skipped when it is not built. Its root version line names this build (known).
LEAN_WT=${WASM_TOOLS_LEAN:-$ROOT/.lake/build/bin/wasm-tools}
btotal=0; bexact=0; bknown=0
check_text() {
  local -a argv=("$@")
  local got up
  set +e
  got=$("$CS" run wasm-tools -- "${argv[@]}" 2>"$work/gerr"; echo "exit $?")
  [[ $got == $'run\nexit 0' ]] && { set -e; return; }
  up=$(cd "$work/cwd" && timeout 20 env -u COLUMNS -u LINES "$WT" "${argv[@]}" </dev/null 2>"$work/uerr"; echo "exit $?")
  set -e
  ttotal=$((ttotal + 1))
  if [[ $got == "$up" ]] && cmp -s "$work/gerr" "$work/uerr"; then texact=$((texact + 1))
  elif grep -qxF -- "${argv[*]}" <<<"$known"; then tknown=$((tknown + 1))
  else
    fail=1; echo "TEXT MISMATCH: ${argv[*]}"
    diff <(printf '%s\n' "$got"; cat "$work/gerr") <(printf '%s\n' "$up"; cat "$work/uerr") | head -8
  fi
  [[ -x $LEAN_WT ]] || return 0
  set +e
  got=$(cd "$work/cwd" && timeout 20 env -u COLUMNS -u LINES "$LEAN_WT" "${argv[@]}" </dev/null 2>"$work/berr"; echo "exit $?")
  set -e
  btotal=$((btotal + 1))
  if [[ $got == "$up" ]] && cmp -s "$work/berr" "$work/uerr"; then bexact=$((bexact + 1))
  elif grep -qxF -- "${argv[*]}" <<<"$known" || [[ ${argv[*]} == -V || ${argv[*]} == --version ]]; then
    bknown=$((bknown + 1))
  else
    fail=1; echo "BINARY TEXT MISMATCH: ${argv[*]}"
    diff <(printf '%s\n' "$got"; cat "$work/berr") <(printf '%s\n' "$up"; cat "$work/uerr") | head -8
  fi
}
while IFS=$'\t' read -r -a line; do
  [[ ${line[0]} == run* ]] && continue
  check_text "${line[@]:1}"
done < <("$CS" corpus wasm-tools)
while read -r -a argv; do
  [[ ${#argv[@]} == 0 || ${argv[0]} == '#'* ]] && continue
  check_text "${argv[@]}"
done < "$(dirname "$0")/wasm-tools-texts.argv"
echo "texts: $texact/$ttotal byte-identical (stdout, stderr, exit), $tknown known differences of the reading"
if [[ -x $LEAN_WT ]]; then
  echo "binary texts ($LEAN_WT): $bexact/$btotal byte-identical, $bknown known (reading or version line)"
else
  echo "binary texts: SKIP ($LEAN_WT not built: lake build wasm-tools)"
fi
exit $fail
