#!/usr/bin/env bash
# `wast` on component binaries: `(component binary "...")` scripts made from the components the
# pinned wasm-tools 1.262.0 encodes for its tests/cli/component-model scripts, run through our
# binary and upstream's (exit statuses compared), plain and with --ignore-error-messages.
#
#   tools/wasm-tools/tests/wast/components.sh [--bin PATH] [--limit N]
#
# Skips when the pinned binary or the source archive is absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
source "$here/../pins.sh"
wt_require_upstream
wt_require_src
bin=$root/.lake/build/bin/wasm-tools
limit=100000
while (($#)); do
  case $1 in
    --bin) bin=$2; shift 2 ;;
    --limit) limit=$2; shift 2 ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done
wt_require_ours "$bin" wasm-tools
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
n=0
for f in "$WT_SRC_DIR"/tests/cli/component-model/*.wast; do
  d=$tmp/j/$(basename "$f" .wast); mkdir -p "$d"
  "$WT_UPSTREAM" json-from-wast "$f" --wasm-dir "$d" >/dev/null 2>&1 || continue
  for w in "$d"/*.wasm; do
    [[ -e $w ]] || continue
    # components only (layer byte 1), valid ones (module/component directives) and others
    [[ $(od -An -tx1 -j6 -N1 "$w" | tr -d ' ') == 01 ]] || continue
    n=$((n + 1)); ((n > limit)) && break 2
    hex=$(od -An -v -tx1 "$w" | tr -d ' \n' | sed 's/\(..\)/\\\1/g')
    printf '(component binary "%s")\n' "$hex" > "$tmp/c$n.wast"
  done
done
same=0 diff=0 isame=0 idiff=0 ok=0 uok=0 ufail=0 bothfail=0
for s in "$tmp"/c*.wast; do
  [[ -e $s ]] || continue
  "$bin" wast "$s" >/dev/null 2>"$tmp/o.err"; orc=$?
  "$WT_UPSTREAM" wast "$s" >/dev/null 2>/dev/null; trc=$?
  if [[ $trc == 0 ]]; then uok=$((uok + 1)); else ufail=$((ufail + 1)); [[ $orc != 0 ]] && bothfail=$((bothfail + 1)); fi
  if [[ $orc == "$trc" ]]; then same=$((same + 1)); [[ $orc == 0 ]] && ok=$((ok + 1)); else diff=$((diff + 1))
    echo "DIFF rc=$orc/$trc $(basename "$s"): $(awk '/^Caused by:/{c=1;next} c&&NF{print;exit}' "$tmp/o.err")"
  fi
  "$bin" wast --ignore-error-messages "$s" >/dev/null 2>&1; orc=$?
  "$WT_UPSTREAM" wast --ignore-error-messages "$s" >/dev/null 2>&1; trc=$?
  [[ $orc == "$trc" ]] && isame=$((isame + 1)) || idiff=$((idiff + 1))
done
echo "upstream accepts $uok: ours accepts $ok; upstream rejects $ufail (invalid components): ours rejects $bothfail (component validation is a subset)"
echo "SUMMARY components $n scripts: wast same=$same (both ok: $ok) diff=$diff; --ignore-error-messages same=$isame diff=$idiff"
