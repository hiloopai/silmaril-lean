#!/usr/bin/env bash
# Differential fuzzing of the Lean `validate`, `print` and `parse` (core modules: the
# wasm-tools-core build; components: compval in this branch's main binary) against pinned
# wasm-tools 1.262.0, on inputs from the generators of this workflow (our `smith`, `mutate`,
# `wit-smith`, and genapi's component generator `wasm-tools-gen-check --component`) and from
# upstream's `smith`.
#
#   WASM_TOOLS_CORE=/abs/path/to/wasm-tools-core-build/wasm-tools \
#     tools/wasm-tools/tests/gen/fuzz-tools.sh [N] [RANDOM_SEED]          (default 100, seed 1)
#
# `WASM_TOOLS_LEAN` (default this checkout's `.lake/build/bin/wasm-tools`) is the binary under
# test for components; `WASM_TOOLS_CORE` the one for core modules (the core part is skipped
# with a message when it is unset: the core validate/print/parse are the wasm-tools-core
# workflow's and are not on this branch). Every upstream call is by absolute path.
#
# Checks (per input; "agree" = same exit status):
#   core-validate        ours and upstream agree on `validate` (our smith, smith with several
#                        memories/tables, smith at Wasm 1.0 against `--features=mvp,mutable-global`,
#                        our mutate, upstream smith with every upstream default feature)
#   core-print-same      our `print` equals upstream's byte for byte                (counted)
#   core-print-rt        upstream `parse` of our `print`, printed by upstream, equals upstream's
#                        print of the input (our text denotes the input)
#   core-print-rtn       the same modulo encoding choices (`wat-norm.py`: empty `else` arms,
#                        index versus expression form of function-index element segments)
#   core-parse           our `parse` of upstream's text, printed by upstream, equals upstream's
#                        print of the input
#   comp-validate        same for components (default features and `--features all`)
#   comp-print-same, comp-print-rt, comp-parse   as for core, on components (wit-smith outputs,
#                        and `wasm-tools-gen-check --component` outputs when that is built)
# Disagreements are kept in $GT_FUZZ_KEEP (default /tmp/gentool-fuzz-failures).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/pins.sh"
gt_require_upstream
root=$(cd "$here/../../../.." && pwd)
WT=${WASM_TOOLS_LEAN:-$root/.lake/build/bin/wasm-tools}
GEN=${WASM_TOOLS_GEN:-$root/.lake/build/bin/wasm-tools-gen}
CHK=$root/.lake/build/bin/wasm-tools-gen-check
CORE=${WASM_TOOLS_CORE:-}
[[ -x $WT ]] || { echo "SKIP: $WT not built (lake build wasm-tools)"; exit 0; }
[[ -x $GEN ]] || GEN=$WT
N=${1:-100}
RANDOM=${2:-1}
keep=${GT_FUZZ_KEEP:-/tmp/gentool-fuzz-failures}
mkdir -p "$keep"
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
cd "$work"
U=$GT_UPSTREAM
declare -A ok bad
keys="core-validate core-print-same core-print-rt core-print-rtn core-parse comp-validate comp-print-same comp-print-rt comp-parse"
for k in $keys; do ok[$k]=0; bad[$k]=0; done
n=0
tally() { if [[ $2 == 0 ]]; then ok[$1]=$((ok[$1]+1)); else bad[$1]=$((bad[$1]+1)); n=$((n+1)); cp "$3" "$keep/$1-$n.wasm" 2>/dev/null; fi; }
mvp="--sign-extension-ops-enabled false --saturating-float-to-int-enabled false \
--multi-value-enabled false --reference-types-enabled false --bulk-memory-enabled false \
--simd-enabled false --relaxed-simd-enabled false --tail-call-enabled false \
--extended-const-enabled false --gc-enabled false --exceptions-enabled false \
--memory64-enabled false"
# one input through validate / print / parse; $1 = core|comp, $2 = file, $3 = validate flags
run_one() {
  local kind=$1 f=$2 vflags=$3 bin
  if [[ $kind == core ]]; then bin=$CORE; else bin=$WT; fi
  # shellcheck disable=SC2086
  "$U" validate $vflags "$f" >/dev/null 2>&1; local us=$?
  # shellcheck disable=SC2086
  "$bin" validate $vflags "$f" >/dev/null 2>&1; local os=$?
  [[ $us == "$os" ]]; tally "$kind-validate" $? "$f"
  [[ $us == 0 ]] || return 0
  "$U" print "$f" > u.wat 2>/dev/null || return 0
  if "$bin" print "$f" > o.wat 2>/dev/null; then
    cmp -s u.wat o.wat; tally "$kind-print-same" $? "$f"
    if "$U" parse o.wat -o rt.wasm 2>/dev/null && "$U" print rt.wasm > rt.wat 2>/dev/null; then
      cmp -s u.wat rt.wat; tally "$kind-print-rt" $? "$f"
      if [[ $kind == core ]]; then
        python3 -I "$here/wat-norm.py" u.wat > un.wat; python3 -I "$here/wat-norm.py" rt.wat > rtn.wat
        cmp -s un.wat rtn.wat; tally core-print-rtn $? "$f"
      fi
    else tally "$kind-print-rt" 1 "$f"; [[ $kind == core ]] && tally core-print-rtn 1 "$f"; fi
  else
    tally "$kind-print-same" 1 "$f"; tally "$kind-print-rt" 1 "$f"
  fi
  if "$bin" parse u.wat -o p.wasm 2>/dev/null && "$U" print p.wasm > p.wat 2>/dev/null; then
    cmp -s u.wat p.wat; tally "$kind-parse" $? "$f"
  else tally "$kind-parse" 1 "$f"; fi
}
upflags="--compact-imports-enabled false --custom-descriptors-enabled false \
--shared-everything-threads-enabled false --wide-arithmetic-enabled false"
[[ -n $CORE && -x $CORE ]] || echo "note: WASM_TOOLS_CORE unset or not executable: core checks skipped"
if [[ -x $CHK ]]; then
  mkdir comps
  (ulimit -v 8000000; "$CHK" --component --count "$N" --size 30 --out comps >/dev/null 2>&1)
fi
for i in $(seq 1 "$N"); do
  head -c $(( (RANDOM * 32768 + RANDOM) % 6000 + 1 )) /dev/urandom > s
  if [[ -n $CORE && -x $CORE ]]; then
    "$GEN" smith s -o a.wasm && run_one core a.wasm ""
    "$GEN" smith s --max-memories 3 --max-tables 3 --generate-custom-sections true -o b.wasm \
      && run_one core b.wasm ""
    # shellcheck disable=SC2086
    "$GEN" smith s $mvp -o c.wasm && run_one core c.wasm "--features=mvp,mutable-global"
    "$GEN" mutate a.wasm -s "$i" -o d.wasm 2>/dev/null && run_one core d.wasm ""
    # shellcheck disable=SC2086
    "$U" smith s $upflags -o e.wasm 2>/dev/null && run_one core e.wasm ""
  fi
  "$GEN" wit-smith s -o w.wasm 2>/dev/null && run_one comp w.wasm ""
  "$GEN" wit-smith s --async --futures --streams --error-context -o x.wasm 2>/dev/null \
    && run_one comp x.wasm "--features all"
  for f in comps/comp-*.wasm; do [[ -e $f ]] || break; done
  cf=$(ls comps 2>/dev/null | sed -n "${i}p")
  [[ -n $cf ]] && run_one comp "comps/$cf" ""
done
fail=0
for k in $keys; do
  printf '%-16s %5d agree %5d differ\n' "$k" "${ok[$k]}" "${bad[$k]}"
  case $k in *validate) [[ ${bad[$k]} == 0 ]] || fail=1 ;; esac
done
[[ $fail == 0 ]]
