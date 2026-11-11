#!/usr/bin/env bash
# Run the `wast` RUN lines of wasm-tools 1.262.0's own tests (tests/cli/**/*.wast) with our
# binary and the pinned upstream binary, from the upstream source root (so `--snapshot
# tests/snapshots` and `tests/testsuite/...` resolve), and compare exit statuses.
#
#   tools/wasm-tools/tests/wast/run-lines.sh [--bin PATH] [--strip-asserts]
#
# `--strip-asserts` drops `--assert`/`--snapshot` (and their values) from every line, which
# compares the directive checks alone (features, round trip, messages).
# Skips (exit 0) when the pinned binary or the source archive is absent. BLESS is unset.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
source "$here/../pins.sh"
wt_require_upstream
wt_require_src
bin=$root/.lake/build/bin/wasm-tools
strip=0
while (($#)); do
  case $1 in
    --bin) bin=$2; shift 2 ;;
    --strip-asserts) strip=1; shift ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done
wt_require_ours "$bin" wasm-tools
bin=$(cd "$(dirname "$bin")" && pwd)/$(basename "$bin")
unset BLESS
same=0 diff=0 both0=0
cd "$WT_SRC_DIR" || exit 1
while IFS=$'\t' read -r -a row; do
  file=${row[0]}
  args=("${row[@]:1}")
  if ((strip)); then
    out=(); skip=0
    for a in "${args[@]}"; do
      if ((skip)); then skip=0; continue; fi
      case $a in
        --assert|--snapshot) skip=1 ;;
        --assert=*|--snapshot=*) ;;
        *) out+=("$a") ;;
      esac
    done
    args=("${out[@]}")
  fi
  timeout 120 "$bin" "${args[@]}" >/dev/null 2>/tmp/run-lines-ours.$$; orc=$?
  timeout 120 "$WT_UPSTREAM" "${args[@]}" >/dev/null 2>/dev/null; trc=$?
  if [[ $orc == "$trc" ]]; then v=SAME; same=$((same + 1)); [[ $orc == 0 ]] && both0=$((both0 + 1))
  else v=DIFF; diff=$((diff + 1)); fi
  printf '%s\t%s\trc=%s/%s\t%s\n' "$v" "$file" "$orc" "$trc" "${args[*]}"
  if [[ $v == DIFF ]]; then
    # the innermost cause of our first failure
    awk '/^Caused by:/{c=1; next} c && (/^$/ || /^----/){exit} c{last=$0} END{if (last != "") print "    cause: " last}' /tmp/run-lines-ours.$$
    head -1 /tmp/run-lines-ours.$$ | sed 's/^/    ours: /'
  fi
done < <(python3 -I "$here/run-lines.py" "$WT_SRC_DIR")
rm -f /tmp/run-lines-ours.$$
echo "SUMMARY run-lines$( ((strip)) && echo ' (asserts stripped)') same=$same (both ok: $both0) diff=$diff"
