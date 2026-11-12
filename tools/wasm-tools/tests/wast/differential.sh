#!/usr/bin/env bash
# Differential test of `json-from-wast` and `wast` against the pinned wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/wast/differential.sh [--bin PATH] [--wast-only|--json-only] FILE.wast|DIR...
#
# Runs every `.wast` file through `PATH json-from-wast F --wasm-dir D` and the pinned
# `wasm-tools json-from-wast F --wasm-dir D'` (stdout compared byte for byte, exit status,
# stderr empty or not, the set of auxiliary file names, and how many auxiliary files are
# byte-identical), and through `wast --ignore-error-messages F` and `wast F` (exit status and
# stderr class). One line per file and command, then a summary. PATH defaults to
# .lake/build/bin/wasm-tools.
#
# The pinned tool is called by absolute path only (never through PATH). When it is absent the
# script prints a skip line and exits 0, so CI without it is unaffected.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
# shellcheck source=../pins.sh
source "$here/../pins.sh"
WT=$WT_UPSTREAM

root=$(cd "$here/../../../.." && pwd)
bin=""
mode=both
files=()
while (($#)); do
  case $1 in
    --bin) bin=$2; shift 2 ;;
    --wast-only) mode=wast; shift ;;
    --json-only) mode=json; shift ;;
    *) files+=("$1"); shift ;;
  esac
done
[[ -n $bin ]] || bin=$root/.lake/build/bin/wasm-tools

wt_require_upstream
wt_require_ours "$bin" wasm-tools

list=()
for f in "${files[@]}"; do
  if [[ -d $f ]]; then while IFS= read -r g; do list+=("$g"); done < <(find "$f" -name '*.wast' | sort)
  else list+=("$f"); fi
done

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
ms() { date +%s%N; }

jsame=0 jdiff=0 bins=0 binsame=0 wsame=0 wdiff=0 wisame=0 widiff=0
tours=0 ttheirs=0
for f in "${list[@]}"; do
  if [[ $mode != wast ]]; then
    rm -rf "$tmp/o" "$tmp/t"; mkdir -p "$tmp/o" "$tmp/t"
    t0=$(ms); "$bin" json-from-wast "$f" --wasm-dir "$tmp/o" >"$tmp/o.json" 2>"$tmp/o.err"; orc=$?; t1=$(ms)
    "$WT" json-from-wast "$f" --wasm-dir "$tmp/t" >"$tmp/t.json" 2>"$tmp/t.err"; trc=$?; t2=$(ms)
    tours=$((tours + (t1 - t0) / 1000000)); ttheirs=$((ttheirs + (t2 - t1) / 1000000))
    oe=$([[ -s $tmp/o.err ]] && echo err || echo -); te=$([[ -s $tmp/t.err ]] && echo err || echo -)
    names=same
    [[ "$(ls "$tmp/o")" == "$(ls "$tmp/t")" ]] || names=differ
    nb=0; ns=0
    for g in "$tmp"/t/*; do
      [[ -e $g ]] || continue
      nb=$((nb + 1)); cmp -s "$g" "$tmp/o/$(basename "$g")" && ns=$((ns + 1))
    done
    bins=$((bins + nb)); binsame=$((binsame + ns))
    if [[ $orc == "$trc" && $oe == "$te" ]] && cmp -s "$tmp/o.json" "$tmp/t.json" && [[ $names == same ]]; then
      verdict=SAME; jsame=$((jsame + 1))
    else
      verdict=DIFF; jdiff=$((jdiff + 1))
    fi
    printf 'json-from-wast\t%s\t%s\trc=%s/%s\tstderr=%s/%s\tfiles=%s\tbytes=%s/%s\t%sms/%sms\n' \
      "$verdict" "$f" "$orc" "$trc" "$oe" "$te" "$names" "$ns" "$nb" \
      $(((t1 - t0) / 1000000)) $(((t2 - t1) / 1000000))
    [[ $verdict == DIFF && -s $tmp/o.err ]] && sed 's/^/    ours: /' "$tmp/o.err" | head -3
  fi
  if [[ $mode != json ]]; then
    for flags in "--ignore-error-messages" ""; do
      "$bin" wast $flags "$f" >/dev/null 2>"$tmp/o.err"; orc=$?
      "$WT" wast $flags "$f" >/dev/null 2>"$tmp/t.err"; trc=$?
      if [[ $orc == "$trc" ]]; then v=SAME; else v=DIFF; fi
      if [[ -n $flags ]]; then
        [[ $v == SAME ]] && wisame=$((wisame + 1)) || widiff=$((widiff + 1))
      else
        [[ $v == SAME ]] && wsame=$((wsame + 1)) || wdiff=$((wdiff + 1))
      fi
      printf 'wast%s\t%s\t%s\trc=%s/%s\n' "${flags:+ $flags}" "$v" "$f" "$orc" "$trc"
      [[ $v == DIFF && -s $tmp/o.err ]] && sed 's/^/    ours: /' "$tmp/o.err" | sed -n '1,4p'
    done
  fi
done
echo "SUMMARY json-from-wast same=$jsame diff=$jdiff aux-bytes-identical=$binsame/$bins time-ours=${tours}ms time-wasm-tools=${ttheirs}ms"
echo "SUMMARY wast --ignore-error-messages same=$wisame diff=$widiff; wast same=$wsame diff=$wdiff"
