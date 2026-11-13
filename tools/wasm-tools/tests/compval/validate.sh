#!/usr/bin/env bash
# Differential test of `wasm-tools validate` on components: our Lean binary against the pinned
# upstream wasm-tools 1.262.0, on every binary of the component `.wast` suites.
#
#   tools/wasm-tools/tests/compval/validate.sh [--out DIR] [--suite cm|wasmtime|wasm-tools|all]
#
# For each `.wast` file, the pinned `wasm-tools json-from-wast` writes the binaries of its
# commands (`module`, `module definition`, `assert_invalid`, `assert_malformed` and
# `assert_unlinkable` in binary form). Each binary is validated by upstream and by
# `.lake/build/bin/wasm-tools-cv validate` under two feature settings:
#
#   all   `--features all`
#   run   the features of the file's `;; RUN:` line (`-f X`), else the default
#
# and the exit statuses are compared (0 = valid, nonzero = invalid; the message text is not
# compared, only its class). One line per binary and setting goes to OUT/results.tsv:
#
#   suite  file  binary  kind  setting  features  expected  upstream  ours  agree
#
# (`kind`: component/module from the preamble; `expected`: what the script says, `valid`
# for `module`, `invalid` for the assertions). OUT/summary.txt has the counts, separately for
# components and core modules (core modules are this driver's stand-in path; the core validator
# belongs to the validate track). Exit 0 after running (disagreements are data), 77 when a
# pinned tool or the binary is absent.
#
# Suites: `cm` = vendor/component-model/d095e2f/test, `wasmtime` =
# vendor/wasmtime-component-wast/component-model, `wasm-tools` = wasm-tools' own
# tests/cli/component-model at 1.262.0 (WT_CM_SRC, default
# ~/.cache/silmaril-tools/src/wasm-tools-1.262.0-cli/wasm-tools-1.262.0; skipped when absent).

set -euo pipefail
root=$(cd "$(dirname "$0")/../../../.." && pwd)
out=
suite=all
while [[ $# -gt 0 ]]; do
  case $1 in
    --out) out=$2; shift 2 ;;
    --suite) suite=$2; shift 2 ;;
    -h|--help) sed -n '2,30p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done

# shellcheck source=../../../wasm-jco/tests/pins.sh
source "$root/tools/wasm-jco/tests/pins.sh"
wt=$WASM_TOOLS
ours=${WASM_TOOLS_LEAN:-$root/.lake/build/bin/wasm-tools-cv}
if [[ ! -x $wt ]]; then
  echo "compval/validate: SKIP: pinned wasm-tools $WASM_TOOLS_VERSION not found at $wt" >&2
  exit 77
fi
if [[ $(sha256sum "$wt" | cut -d' ' -f1) != "$WASM_TOOLS_SHA256" ]]; then
  echo "compval/validate: SKIP: $wt does not have the pinned SHA-256 $WASM_TOOLS_SHA256" >&2
  exit 77
fi
if [[ ! -x $ours ]]; then
  echo "compval/validate: SKIP: $ours missing (lake build wasm-tools-cv)" >&2
  exit 77
fi
wts=${WT_CM_SRC:-$HOME/.cache/silmaril-tools/src/wasm-tools-1.262.0-cli/wasm-tools-1.262.0}

[[ -n $out ]] || out=$(mktemp -d /tmp/compval-validate.XXXXXX)
mkdir -p "$out"
res=$out/results.tsv
printf 'suite\tfile\tbinary\tkind\tsetting\tfeatures\texpected\tupstream\tours\tagree\n' > "$res"

suite_dir() {
  case $1 in
    cm) echo "$root/vendor/component-model/d095e2f/test" ;;
    wasmtime) echo "$root/vendor/wasmtime-component-wast/component-model" ;;
    wasm-tools) echo "$wts/tests/cli/component-model" ;;
  esac
}
case $suite in
  all) suites=(cm wasmtime wasm-tools) ;;
  *) suites=("$suite") ;;
esac

kind_of() {
  local v
  v=$(od -An -tx1 -j4 -N4 "$1" 2>/dev/null | tr -d " \n")
  case $v in
    01000000) echo module ;;
    0d000100) echo component ;;
    *) echo other ;;
  esac
}

rc_of() { set +e; "$@" >/dev/null 2>&1; local r=$?; set -e; [[ $r == 0 ]] && echo 0 || echo 1; }

for s in "${suites[@]}"; do
  d=$(suite_dir "$s")
  if [[ ! -d $d ]]; then echo "compval/validate: suite $s absent ($d), skipped" >&2; continue; fi
  while IFS= read -r f; do
    rel=${f#"$d"/}
    w=$out/wasm/$s/${rel%.wast}
    mkdir -p "$w"
    if ! "$wt" json-from-wast "$f" -o "$w/t.json" --wasm-dir "$w/" >/dev/null 2>"$w/json.err"; then
      printf '%s\t%s\t-\t-\t-\t-\t-\t-\t-\tjson-from-wast-failed\n' "$s" "$rel" >> "$res"
      continue
    fi
    runf=$(grep -m1 '^;; RUN:' "$f" | grep -oE '(-f|--features)[= ][^ ]+' | head -1 | sed -E 's/^(-f|--features)[= ]//' || true)
    jq -r '.commands[] | select(.filename != null and .module_type != "text") |
      [.filename, (if .type == "module" or .type == "module_definition" then "valid" else "invalid" end)] | @tsv' \
      "$w/t.json" | while IFS=$'\t' read -r bin expected; do
      p=$w/$bin
      [[ -f $p ]] || continue
      k=$(kind_of "$p")
      for setting in all run; do
        if [[ $setting == all ]]; then fl=(--features all); fs=all
        elif [[ -n $runf ]]; then fl=(--features "$runf"); fs=$runf
        else fl=(); fs=default; fi
        u=$(rc_of "$wt" validate "${fl[@]}" "$p")
        o=$(rc_of timeout 120 "$ours" validate "${fl[@]}" "$p")
        a=$([[ $u == "$o" ]] && echo yes || echo NO)
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$s" "$rel" "$bin" "$k" "$setting" "$fs" \
          "$expected" "$u" "$o" "$a" >> "$res"
      done
    done
  done < <(find "$d" -name '*.wast' | sort)
done

{
  echo "results: $res"
  for k in component module other; do
    awk -F'\t' -v k="$k" 'NR > 1 && $4 == k {
        n[$5]++; if ($10 == "yes") a[$5]++
        if ($10 == "NO" && $8 == 0) fr[$5]++    # upstream valid, ours rejects
        if ($10 == "NO" && $8 != 0) fa[$5]++    # upstream invalid, ours accepts
      }
      END { for (s in n) printf "%s %s: %d binaries, %d agree, %d we reject but upstream accepts, %d we accept but upstream rejects\n", k, s, n[s], a[s], fr[s], fa[s] }' "$res"
  done
  awk -F'\t' 'NR > 1 && $10 == "json-from-wast-failed"' "$res" | wc -l | sed 's/^/json-from-wast failures: /'
} | tee "$out/summary.txt"
