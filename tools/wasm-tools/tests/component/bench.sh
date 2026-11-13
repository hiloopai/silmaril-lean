#!/usr/bin/env bash
# Performance of the Lean `wasm-tools component …` against the pinned upstream 1.262.0, on
# inputs from about 1 KB to several MB. Skips (exit 0) when either binary is absent.
#
#   tools/wasm-tools/tests/component/bench.sh [MAX_SECONDS]
#
# For each case prints the input size, upstream's and our wall time (best of 3) and checks that
# the two outputs agree (bytes for embed/unbundle/wit, exit status for targets, the world for
# new). Regression test: exit 1 when one of our runs takes longer than MAX_SECONDS (default 20)
# or an output disagrees.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
source "$here/pins.sh"
wtc_require_upstream
OURS=${WASM_TOOLS_LEAN:-$repo/.lake/build/bin/wasm-tools}
if [[ ! -x $OURS ]]; then echo "SKIP: $OURS not built (lake build wasm-tools)"; exit 0; fi
WT=$WT_UPSTREAM
MAX=${1:-20}
tmp=$(mktemp -d /tmp/wasm-tools-comp-bench-XXXXXX)
trap 'rm -rf "$tmp"' EXIT
cd "$tmp"

# best of three wall-clock times, in seconds
best() {
  local b=999999 t
  for _ in 1 2 3; do
    local s; s=$(date +%s.%N)
    "$@" >/dev/null 2>&1
    t=$(echo "$(date +%s.%N) - $s" | bc)
    b=$(echo "if ($t < $b) $t else $b" | bc)
  done
  printf '%.3f' "$b"
}

# A world with an interface of N functions over strings and records.
gen_wit() {
  local n=$1
  {
    echo "package bench:p$n;"
    echo "interface api {"
    echo "  record pt { x: u32, y: string }"
    for ((i = 0; i < n; i++)); do echo "  op$i: func(a: string, b: pt) -> list<u8>;"; done
    echo "}"
    echo "world w {"
    echo "  import api;"
    for ((i = 0; i < n; i++)); do echo "  export run$i: func(x: u32) -> u32;"; done
    echo "}"
  } >"w$n.wit"
}

# A core module for world wN with a data segment of D bytes (the module size knob).
gen_core() {
  local n=$1 d=$2
  "$WT" component embed "w$n.wit" --dummy -o "d$n.wasm"
  "$WT" print "d$n.wasm" | sed '$d' >"c$n-$d.wat"
  python3 -I -c "import sys; sys.stdout.write('(data \"' + 'ab' * ($d // 2) + '\")\n)\n')" >>"c$n-$d.wat"
  "$WT" parse "c$n-$d.wat" -o "e$n-$d.wasm"
  "$WT" strip "e$n-$d.wasm" -o "c$n-$d.wasm"
}

fail=0
row() { printf '%-10s %-28s %10s %9s %9s %7s %s\n' "$@"; }
row command input bytes upstream ours ratio agree
check_time() { if (( $(echo "$1 > $MAX" | bc) )); then fail=1; fi; }
ratio() { echo "scale=1; $2 / ($1 + 0.0005)" | bc; }

for spec in "4 0" "64 0" "64 1000000" "512 4000000"; do
  set -- $spec; n=$1; d=$2
  gen_wit "$n"; gen_core "$n" "$d"
  in="c$n-$d.wasm"; sz=$(stat -c %s "$in")
  # embed
  tu=$(best "$WT" component embed "w$n.wit" "$in" -o eu.wasm)
  to=$(best "$OURS" component embed "w$n.wit" "$in" -o eo.wasm)
  ok=yes; cmp -s eu.wasm eo.wasm || { ok=no; fail=1; }
  row embed "w$n.wit + $in" "$sz" "$tu" "$to" "$(ratio "$tu" "$to")" "$ok"; check_time "$to"
  # new
  tu=$(best "$WT" component new eu.wasm -o nu.wasm)
  to=$(best "$OURS" component new eu.wasm -o no.wasm)
  ok=yes
  "$WT" component wit nu.wasm >nu.wit 2>/dev/null; "$WT" component wit no.wasm >no.wit 2>/dev/null
  cmp -s nu.wit no.wit || { ok=no; fail=1; }
  row new "embedded $in" "$(stat -c %s eu.wasm)" "$tu" "$to" "$(ratio "$tu" "$to")" "$ok (world)"; check_time "$to"
  # wit of a component
  tu=$(best "$WT" component wit nu.wasm)
  to=$(best "$OURS" component wit nu.wasm)
  "$OURS" component wit nu.wasm >wo.wit 2>/dev/null
  ok=yes; cmp -s nu.wit wo.wit || { ok=no; fail=1; }
  row wit "component of $in" "$(stat -c %s nu.wasm)" "$tu" "$to" "$(ratio "$tu" "$to")" "$ok"; check_time "$to"
  # wit text and --wasm
  tu=$(best "$WT" component wit --wasm "w$n.wit" -o wu.wasm)
  to=$(best "$OURS" component wit --wasm "w$n.wit" -o wo.wasm)
  ok=yes; cmp -s wu.wasm wo.wasm || { ok=no; fail=1; }
  row wit--wasm "w$n.wit" "$(stat -c %s "w$n.wit")" "$tu" "$to" "$(ratio "$tu" "$to")" "$ok"; check_time "$to"
  # targets
  tu=$(best "$WT" component targets "w$n.wit" nu.wasm)
  to=$(best "$OURS" component targets "w$n.wit" nu.wasm)
  "$WT" component targets "w$n.wit" nu.wasm >/dev/null 2>&1; ue=$?
  "$OURS" component targets "w$n.wit" nu.wasm >/dev/null 2>&1; oe=$?
  ok=yes; [[ $ue == "$oe" ]] || { ok=no; fail=1; }
  row targets "component of $in" "$(stat -c %s nu.wasm)" "$tu" "$to" "$(ratio "$tu" "$to")" "$ok"; check_time "$to"
  # unbundle
  tu=$(best "$WT" component unbundle --module-dir mu --threshold 0 nu.wasm -o uu.wasm)
  to=$(best "$OURS" component unbundle --module-dir mo --threshold 0 nu.wasm -o uo.wasm)
  ok=yes; { cmp -s uu.wasm uo.wasm && diff -rq mu mo >/dev/null; } || { ok=no; fail=1; }
  row unbundle "component of $in" "$(stat -c %s nu.wasm)" "$tu" "$to" "$(ratio "$tu" "$to")" "$ok"; check_time "$to"
done
# Types of exponential size (`16^8` leaves: eight records of sixteen fields nested): `embed
# --dummy` stops flattening at the limit (DummyFast), `new` and `wit --wasm` stop at wasmparser's
# type-size budget (Budget). Without them neither finished.
deep() {
  local k=$1
  {
    echo "package a:b;"
    echo "world records {"
    for ((i = 1; i <= 8; i++)); do
      local t="t$((i + 1))"; [[ $i == 8 ]] && t=u8
      printf '  record t%d {' "$i"
      for ((f = 1; f <= k; f++)); do printf ' f%d: %s,' "$f" "$t"; done
      echo " }"
    done
    echo "  import x: func(t: t1);"
    echo "}"
  } >"deep$k.wit"
}
deep 16
tu=$(best "$WT" component embed --dummy deep16.wit -o du.wasm)
to=$(best "$OURS" component embed --dummy deep16.wit -o do.wasm)
ok=yes; cmp -s du.wasm do.wasm || { ok=no; fail=1; }
row embed--dummy deep16.wit "$(stat -c %s deep16.wit)" "$tu" "$to" "$(ratio "$tu" "$to")" "$ok"; check_time "$to"
tu=$(best "$WT" component new du.wasm -o /dev/null)
to=$(best "$OURS" component new du.wasm -o /dev/null)
"$WT" component new du.wasm -o /dev/null 2>ue.txt; ue=$?
"$OURS" component new du.wasm -o /dev/null 2>oe.txt; oe=$?
ok=yes; { [[ $ue == "$oe" && $ue != 0 ]] && cmp -s ue.txt oe.txt; } || { ok=no; fail=1; }
row new "dummy of deep16.wit" "$(stat -c %s du.wasm)" "$tu" "$to" "$(ratio "$tu" "$to")" "$ok (refused)"; check_time "$to"
tu=$(best "$WT" component wit --wasm deep16.wit)
to=$(best "$OURS" component wit --wasm deep16.wit)
"$WT" component wit --wasm deep16.wit -o /dev/null 2>ue.txt; ue=$?
"$OURS" component wit --wasm deep16.wit -o /dev/null 2>oe.txt; oe=$?
ok=yes; { [[ $ue == "$oe" && $ue != 0 ]] && cmp -s ue.txt oe.txt; } || { ok=no; fail=1; }
row wit--wasm deep16.wit "$(stat -c %s deep16.wit)" "$tu" "$to" "$(ratio "$tu" "$to")" "$ok (refused)"; check_time "$to"
exit $fail
