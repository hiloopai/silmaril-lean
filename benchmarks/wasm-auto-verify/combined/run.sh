#!/usr/bin/env bash
# The combined benchmark of docs/projects/wasm-binaryen-tooling.md: time, memory and success rate of the
# automatic checks on pinned inputs, kept as a regression test.
#
#   benchmarks/wasm-auto-verify/combined/run.sh [--certs] [--mor] [--all]
#
# Rows (each one command under /usr/bin/time: wall seconds, peak resident memory):
#   front-bench    `wasm-check bench`: the 21 cases of Silmaril.Wasm.Auto.FrontBenchX.allCases
#                  (first set: WasmSpec Max, Adder, SumTo; div10 and requant kernels; mutants;
#                  extended set: requant against Binaryen -O2, an Adler-32 8-way step, division with
#                  traps, a global counter, through the extended summaries)
#   pass-O2        `wasm-check pass` on Binaryen version_123 -O2 of the e-graph corpus
#                  (tools/wasm-egraph/corpus/opt-in*.wasm), with e-graph lifts (TvBinaryen)
#   pass-peep      the same for wasm-opt --neutral-ops --eqz-pair (TvPeep)
#   pass-O3        the same for Binaryen -O3 on 60 random functions (rand60*.wasm, TvRandom)
#   lean-front     `lake env lean tests/wasm/auto/FrontBench/Thms.lean` (the benchmark's Lean
#                  theorems: refutations, equivalences, reference functions)
#   lean-frontx    `lake env lean` of the extended set's proof modules (tests/wasm/auto/FrontBenchX/Proofs/*)
#   lean-kernel    the memory cases, kernel-checked (tests/wasm/auto2/KernelBench/Proofs/Adler.lean)
# With --certs, the `pass` certificates of pass-O2 and pass-peep (one Lean file per optimizer run:
# the proved exports by `modEquiv_of_checkAll`, the lifted ones by `modEquiv_of_egraph`) are
# checked with `lake env lean`; their lifts count as proved only then. The proved exports
# are checked in chunks (`--chunk`, one kernel evaluation of checkAmong per chunk); pass-O3's
# certificate is still not checked (decoding the modules in the kernel is too large). With --all, also
# tools/wasm-egraph/tests/run.sh and benchmarks/wasm-auto-verify/vcgen/run.sh --quick.
# Pass 3 (kernel track): every certificate links each binary to its WAT module: `--link` (`rfl`) for
# the Binaryen-written outputs, `--link-equiv` (kernel-checked equivalence at every proved export,
# and the certificate transferred to the decoded modules) for the inputs and the wasm-opt
# output; validation through `Silmaril.Wasm.Auto2.Valid2` (`validG?`).
# Pass 2 (kernel track): chunks of 60 exports by default (CHUNK overrides): with the validation-free
# instance each chunk costs one instantiation, and larger chunks no longer raise the peak memory.
# Round 2 (kernel track): every `pass` certificate gives its modules as WAT text (`wat3b!`, which
# also reads Binaryen's `tuple.make` of the opt-in corpus), so none decodes a binary in the kernel.
# With --mor, a certificate is checked by `lake build --scratch` (a copy as a fresh
# scratch module with a new content hash, removed afterwards), under its memory cap, instead of
# `lake env lean`; so are the lean-* rows. Pass 2 (kernel track): before `--scratch`, the copies had
# the same content as an earlier run's, so Lake's artifact cache restored them and the reported
# certificate times (about 3 s) were cache restores, not kernel checks.
#
# Expected verdict counts: expected.tsv (set, proved, refuted, unknown). Output: a Markdown table
# on stdout and in .lake/bench/wasm-auto-verify/combined/table.md. Needs the executable
# wasm-check (`lake build wasm-check`); skips with a message (exit 0) without it.
# Exit status: 0 when every count is the expected one, 1 otherwise.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
cd "$root"
bin=${SIL_WASM_CHECK:-$root/.lake/build/bin/wasm-check}
certs=0
all=0
mor=0
for a in "$@"; do
  case $a in
    --certs) certs=1 ;;
    --all) all=1 ;;
    --mor) mor=1 ;;
    *) echo "usage: $0 [--certs] [--mor] [--all]" >&2; exit 2 ;;
  esac
done
if [[ ! -x $bin ]]; then
  echo "SKIP: $bin not found (build it with lake build wasm-check)"
  exit 0
fi
[[ -x /usr/bin/time ]] || { echo "SKIP: /usr/bin/time not found"; exit 0; }
out=.lake/bench/wasm-auto-verify/combined
mkdir -p "$out"
C=tools/wasm-egraph/corpus
rows=()
fail=0

expected() { awk -F'\t' -v s="$1" '$1 == s { print $2 "\t" $3 "\t" $4 }' "$here/expected.tsv"; }
timeof() { tail -1 "$1" | awk '{ printf "%.1f\t%d\n", $1, $2 / 1024 }'; }
row() { # set cases proved refuted unknown timefile test
  local set=$1 n=$2 p=$3 r=$4 u=$5 tf=$6 test=$7 t m want
  read -r t m < <(timeof "$tf")
  local rate=$(( n > 0 ? 100 * (p + r) / n : 0 ))
  want=$(expected "$set")
  if [[ -n $want && $want != "$p"$'\t'"$r"$'\t'"$u" ]]; then
    echo "FAIL $set: proved/refuted/unknown $p/$r/$u, expected $(tr '\t' / <<< "$want")"; fail=1
  fi
  rows+=("| $set | $n | $p | $r | $u | $rate % | $t | $m | $test |")
}

# 1. The front-end cases.
/usr/bin/time -f '%e %M' -o "$out/bench.time" "$bin" bench > "$out/bench.tsv" || true
p=$(grep -c $'\t"proved"\t' "$out/bench.tsv" || true)
r=$(grep -c $'\t"refuted"\t' "$out/bench.tsv" || true)
u=$(grep -c $'\t"unknown"\t' "$out/bench.tsv" || true)
row front-bench $((p + r + u)) "$p" "$r" "$u" "$out/bench.time" '`wasm-check bench`'

# 2. Optimizer runs.
checker='lake env lean'
(( mor )) && checker='lake build'
# Check the certificate of a set (its time in $out/$set.cert.time).
checkcert() {
  local set=$1
  if (( mor )); then
    /usr/bin/time -f '%e %M' -o "$out/$set.cert.time" lake build \
      --scratch "$out/$set.lean"
    return
  fi
  /usr/bin/time -f '%e %M' -o "$out/$set.cert.time" timeout 3600 lake env lean "$out/$set.lean"
}
pass() { # set in out tv cert|nocert [wat [link [link-equiv]]]
  local set=$1 in=$2 o=$3 tv=$4 mode=$5 wat=${6:-} link=${7:-} lequiv=${8:-} s p r u l watargs=()
  if [[ -n $wat ]]; then
    # The certificate's modules as WAT text (pinned prints of the binaries, gen-wat.sh).
    (cd "$C" && sha256sum --quiet -c "$here/wat/SOURCES") ||
      { echo "FAIL $set: wat/SOURCES does not match the corpus"; fail=1; }
    watargs=(--wat "$here/wat/${in%.wasm}.wat" "$here/wat/${o%.wasm}.wat")
    # Pass 2 (kernel track): the certificate proves by `rfl` that the WAT module of each named
    # side is the module the tool decoded from its binary (`--link`; Binaryen-written binaries).
    [[ -n $link && $link != - ]] && watargs+=(--link "$link")
    # Pass 3 (kernel track): for binaries Binaryen did not write (Binaryen's printer reorders and
    # merges their type sections, so `--link`'s `rfl` fails), `--link-equiv` proves each proved
    # export of the decoded module equivalent to the WAT module's and transfers the certificate's
    # equivalences to the decoded modules (`decA_<j>`, `decB_<j>`, `decAB_<j>`).
    [[ -n $lequiv ]] && watargs+=(--link-equiv "$lequiv")
  fi
  /usr/bin/time -f '%e %M' -o "$out/$set.time" "$bin" pass "$C/$in" "$C/$o" --random 200 \
    --egraph-tv "$tv" --lean "$out/$set.lean" --chunk "${CHUNK:-60}" "${watargs[@]}" > "$out/$set.jsonl"
  s=$(grep '"summary"' "$out/$set.jsonl" | tail -1)
  n=$(sed -E 's/.*"exports":([0-9]+).*/\1/' <<< "$s")
  p=$(sed -E 's/.*"proved":([0-9]+).*/\1/' <<< "$s")
  r=$(sed -E 's/.*"refuted":([0-9]+).*/\1/' <<< "$s")
  u=$(sed -E 's/.*"unknown":([0-9]+).*/\1/' <<< "$s")
  l=$(sed -E 's/.*"egraphLifts":([0-9]+).*/\1/' <<< "$s")
  if [[ -n $lequiv ]]; then
    s=$(grep '"summary"' "$out/$set.jsonl" | tail -1)
    local le
    le=$(grep -o '"linked":[0-9]*' "$out/$set.jsonl" | cut -d: -f2)
    if [[ $le != "$(sed -E 's/.*"proved":([0-9]+).*/\1/' <<< "$s")" ]]; then
      echo "FAIL $set: --link-equiv linked ${le:-0} exports, not every proved one"; fail=1
    fi
  fi
  if (( certs )) && [[ $mode == cert ]]; then
    if checkcert "$set" > "$out/$set.cert.log" 2>&1; then
      p=$((p + l)); u=$((u - l))
      rows+=("| $set certificate | $((p + r)) theorems | | | | | $(timeof "$out/$set.cert.time" | tr '\t' ' ' | awk '{print $1 " | " $2}') | \`$checker\` |")
    else
      echo "FAIL $set: certificate rejected (see $out/$set.cert.log)"; fail=1
    fi
  else
    echo "note: $set: $l e-graph lifts not checked (certificate not run)"
  fi
  local key=$set
  if (( certs )) && [[ $mode == cert ]]; then key=$set+certs; fi
  row "$key" "$n" "$p" "$r" "$u" "$out/$set.time" "\`wasm-check pass\` $o"
}
pass pass-O2 opt-in.wasm opt-in.binaryen-O2.wasm tests/wasm/auto/EGraph/TvBinaryen.lean cert wat b a
pass pass-peep opt-in.wasm opt-in.peep.wasm tests/wasm/auto/EGraph/TvPeep.lean cert wat - ab
# One kernel evaluation of `checkAll` over the 60 random functions of the -O3 certificate
# exceeded 50 GB. Decoding the 2 KB binaries in the kernel is the cost
# (over 16 GiB for one module), so the certificate gives the modules as WAT text instead (wat/,
# Binaryen's printing of the pinned binaries, checked against wat/SOURCES) and checks in chunks.
pass pass-O3 rand60.wasm rand60.binaryen-O3.wasm tests/wasm/auto/EGraph/TvRandom.lean cert wat b a

# 3. The Lean theorems of the front-end benchmark. With --mor, each file is copied to a scratch
# module (so that it is elaborated again, not restored from the build cache) and built by
# `lake build`.
leancheck() { # set file...
  local set=$1 rc=0 f mods=() n=0
  shift
  if (( mor )); then
    /usr/bin/time -f '%e %M' -o "$out/$set.time" lake build --scratch "$@" \
      > "$out/$set.log" 2>&1 || rc=$?
    return $rc
  fi
  /usr/bin/time -f '%e %M' -o "$out/$set.time" bash -c \
    'for f in "$@"; do lake env lean "$f" || exit 1; done' _ "$@" > "$out/$set.log" 2>&1
}
if leancheck lean-front tests/wasm/auto/FrontBench/Thms.lean; then
  row lean-front 13 6 7 0 "$out/lean-front.time" "\`$checker\` …/FrontBench/Thms.lean"
else
  echo "FAIL lean-front (see $out/lean-front.log)"; fail=1
fi
if leancheck lean-frontx tests/wasm/auto/FrontBenchX/Proofs/Proved.lean \
    tests/wasm/auto/FrontBenchX/Proofs/Refuted.lean; then
  row lean-frontx 6 "$(grep -c '^theorem' tests/wasm/auto/FrontBenchX/Proofs/Proved.lean)" \
    "$(grep -c '^theorem' tests/wasm/auto/FrontBenchX/Proofs/Refuted.lean)" 0 \
    "$out/lean-frontx.time" "\`$checker\` …/FrontBenchX/{Proved,Refuted}.lean"
else
  echo "FAIL lean-frontx (see $out/lean-frontx.log)"; fail=1
fi
# Round 2 (kernel track): the memory cases adlersum8-O2 (proved) and adlersum8-mutant (refuted),
# kernel-checked over Silmaril.Wasm.Auto2.Kernel.
if leancheck lean-kernel tests/wasm/auto2/KernelBench/Proofs/Adler.lean; then
  row lean-kernel 2 1 1 0 "$out/lean-kernel.time" "\`$checker\` …/KernelBench/Proofs/Adler.lean"
else
  echo "FAIL lean-kernel (see $out/lean-kernel.log)"; fail=1
fi

# 4. The other tracks' regression tests.
if (( all )); then
  if /usr/bin/time -f '%e %M' -o "$out/egraph.time" tools/wasm-egraph/tests/run.sh \
      > "$out/egraph.log" 2>&1; then
    rows+=("| egraph tests | | | | | ok | $(timeof "$out/egraph.time" | tr '\t' ' ' | awk '{print $1 " | " $2}') | \`tools/wasm-egraph/tests/run.sh\`: $(tail -1 "$out/egraph.log" | grep -o '[0-9]* of [0-9]* functions proved') |")
  else
    echo "FAIL egraph tests (see $out/egraph.log)"; fail=1
  fi
  if /usr/bin/time -f '%e %M' -o "$out/vcgen.time" benchmarks/wasm-auto-verify/vcgen/run.sh --quick \
      > "$out/vcgen.log" 2>&1; then
    rows+=("| vcgen bench (quick) | | | | | ok | $(timeof "$out/vcgen.time" | tr '\t' ' ' | awk '{print $1 " | " $2}') | \`benchmarks/wasm-auto-verify/vcgen/run.sh --quick\` |")
  else
    echo "FAIL vcgen bench (see $out/vcgen.log)"; fail=1
  fi
fi

{
  echo "| Set | Cases | Proved | Refuted | Unknown | Decided | Wall s | Peak MiB | Command |"
  echo "| --- | --- | --- | --- | --- | --- | --- | --- | --- |"
  printf '%s\n' "${rows[@]}"
} | tee "$out/table.md"
if (( fail )); then echo "FAILED"; exit 1; fi
echo "all counts as expected"
