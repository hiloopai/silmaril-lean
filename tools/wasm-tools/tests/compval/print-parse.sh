#!/usr/bin/env bash
# Round trips of `wasm-tools print` / `wasm-tools parse` on components: our Lean binary
# (`.lake/build/bin/wasm-tools-cv`) and the pinned upstream wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/compval/print-parse.sh [--out DIR] DIR_OR_FILE...
#
# Every component binary (`*.wasm` whose preamble is a component's) under the arguments is
# checked; for a binary B:
#
#   print     ours `print B` succeeds iff upstream's does (class agreement)
#   rt        ours `parse (print B)` = B2 succeeds, and ours `print B2` is the text ours prints
#             for B without its `component-name` section (`parse` resolves `$` names and
#             writes no name section; on name-free text this is the proved round trip
#             `Layout.read_printW`, observed through the tool)
#   valid     upstream `validate --features all` agrees on B and B2
#   up-parse  when the text has no core module (upstream does not read `(core module binary
#             …)`): upstream `parse (ours print B)`, without the name section it writes for the
#             `$` names, gives exactly the bytes B2
#   ours-up   ours `parse (upstream print B)` = B4 succeeds, and once custom sections are
#             removed (`wasm-tools strip -a`: our reader drops `$` names instead of writing a
#             name section) upstream prints B4 exactly as it prints B (our reader on upstream's
#             spelling: `$` names, `(;i;)` comments, inline abbreviations, core modules in text)
#   same      ours `print B` is byte-identical to upstream's (wasmprinter's layout, comments
#             and names; core modules are printed in binary, so only binaries without core
#             modules can agree: `nocore` says which)
#   nocore    upstream's text has no core module
#
# One line per binary goes to OUT/results.tsv; OUT/summary.txt has the counts. Exit 0 after
# running; 77 when a pinned tool or the binary is absent.

set -euo pipefail
root=$(cd "$(dirname "$0")/../../../.." && pwd)
out=
inputs=()
while [[ $# -gt 0 ]]; do
  case $1 in
    --out) out=$2; shift 2 ;;
    -h|--help) sed -n '2,24p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) inputs+=("$1"); shift ;;
  esac
done
# shellcheck source=../../../wasm-jco/tests/pins.sh
source "$root/tools/wasm-jco/tests/pins.sh"
wt=$WASM_TOOLS
ours=${WASM_TOOLS_LEAN:-$root/.lake/build/bin/wasm-tools-cv}
if [[ ! -x $wt || $(sha256sum "$wt" | cut -d' ' -f1) != "$WASM_TOOLS_SHA256" ]]; then
  echo "compval/print-parse: SKIP: pinned wasm-tools $WASM_TOOLS_VERSION not found at $wt" >&2
  exit 77
fi
if [[ ! -x $ours ]]; then
  echo "compval/print-parse: SKIP: $ours missing (lake build wasm-tools-cv)" >&2
  exit 77
fi
[[ ${#inputs[@]} -gt 0 ]] || inputs=("$root/tests/wat/fixtures" "$root/examples/wasip3-rust/dist")
[[ -n $out ]] || out=$(mktemp -d /tmp/compval-print-parse.XXXXXX)
mkdir -p "$out/tmp"
res=$out/results.tsv
printf 'binary\tprint\trt\tvalid\tup-parse\tours-up\tsame\tnocore\n' > "$res"
t=$out/tmp

ok() { set +e; "$@" >/dev/null 2>&1; local r=$?; set -e; [[ $r == 0 ]]; }

while IFS= read -r b; do
  [[ $(od -An -tx1 -j4 -N4 "$b" 2>/dev/null | tr -d ' \n') == 0d000100 ]] || continue
  pr=no rt=- va=- up=- ou=- same=- nocore=-
  uo=0; ok "$wt" print "$b" -o "$t/up.wat" || uo=1
  oo=0; ok "$ours" print "$b" -o "$t/ours.wat" || oo=1
  [[ $uo == "$oo" ]] && pr=yes
  if [[ $oo == 0 ]]; then
    rt=no
    if ok "$ours" parse "$t/ours.wat" -o "$t/b2.wasm" && ok "$ours" print "$t/b2.wasm" -o "$t/ours2.wat" \
      && ok "$wt" strip -d component-name "$b" -o "$t/nn.wasm" && ok "$ours" print "$t/nn.wasm" -o "$t/oursnn.wat" \
      && cmp -s "$t/oursnn.wat" "$t/ours2.wat"; then rt=yes; fi
    if [[ $rt == yes ]]; then
      va=no
      v1=0; ok "$wt" validate --features all "$b" || v1=1
      v2=0; ok "$wt" validate --features all "$t/b2.wasm" || v2=1
      [[ $v1 == "$v2" ]] && va=yes
      if ! grep -qE '\(core module .*binary "' "$t/ours.wat"; then
        up=no
        ok "$wt" parse "$t/ours.wat" -o "$t/b3.wasm" && ok "$wt" strip -d component-name "$t/b3.wasm" -o "$t/b3s.wasm" \
          && cmp -s "$t/b2.wasm" "$t/b3s.wasm" && up=yes
      fi
    fi
    if [[ $uo == 0 ]]; then
      cmp -s "$t/up.wat" "$t/ours.wat" && same=yes || same=no
      grep -q '(core module' "$t/up.wat" && nocore=no || nocore=yes
    fi
  fi
  if [[ $uo == 0 ]]; then
    ou=no
    if ok "$ours" parse "$t/up.wat" -o "$t/b4.wasm" && ok "$wt" strip -a "$t/b4.wasm" -o "$t/s4.wasm" \
      && ok "$wt" strip -a "$b" -o "$t/s1.wasm" && ok "$wt" print "$t/s4.wasm" -o "$t/up4.wat" \
      && ok "$wt" print "$t/s1.wasm" -o "$t/up1.wat" && cmp -s "$t/up1.wat" "$t/up4.wat"; then ou=yes; fi
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$pr" "$rt" "$va" "$up" "$ou" "$same" "$nocore" >> "$res"
done < <(find "${inputs[@]}" -name '*.wasm' | sort)

{
  echo "results: $res"
  awk -F'\t' 'NR > 1 { n++
      for (i = 2; i <= 7; i++) { if ($i == "yes") y[i]++; else if ($i == "no") f[i]++ } }
    END { split("binary print rt valid up-parse ours-up same", h, " ")
      printf "%d component binaries\n", n
      for (i = 2; i <= 7; i++) printf "%-9s yes %d, no %d, n/a %d\n", h[i], y[i], f[i], n - y[i] - f[i] }' "$res"
  awk -F'\t' 'NR > 1 && $8 == "yes" { n++; if ($7 == "yes") y++ }
    END { printf "same on binaries without core modules: %d of %d\n", y, n }' "$res"
} | tee "$out/summary.txt"
