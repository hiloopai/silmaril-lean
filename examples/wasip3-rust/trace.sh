#!/usr/bin/env bash
# Run hello.wasm (and the other examples) on silmaril's Core 3.0 interpreter under den's
# callback driver with scripted hosts (tools/wasip3-trace), and check the facts the Lean
# development states about the real call sequence of hello (HelloCore.Thms):
#   * the third world call is future.read (Task.coreFreadFirst, tested here);
#   * no waitable-set.poll and nothing outside den's fragment is called;
#   * run returns ok (task.return [0]) and EXITs.
# Usage: examples/wasip3-rust/trace.sh   (after `lake build wasip3-trace`)
set -u
cd "$(dirname "$0")/../.."
exe=.lake/build/bin/wasip3-trace
if [[ ! -x $exe ]]; then
  echo "SKIP: $exe not built (run lake build wasip3-trace)"; exit 0
fi
fail=0
for host in "" "--fread blocked" "--write blocked" "--fread blocked --write blocked" "--write half"; do
  # shellcheck disable=SC2086
  out=$($exe examples/wasip3-rust/dist/hello.wasm $host 2>&1)
  third=$(grep '^  world:' <<<"$out" | sed -n 3p)
  ok=1
  [[ $third == *'$root#future.read(3)'* ]] || ok=0
  grep -q 'UNSUPPORTED\|outside den\|poll' <<<"$out" && ok=0
  grep -q '^EXIT task.return=(some \[0\])' <<<"$out" || ok=0
  calls=$(grep -c '^call ' <<<"$out")
  if [[ $ok == 1 ]]; then echo "ok   hello ${host:-(eager host)}: $calls calls, third world call future.read(3)"
  else echo "FAIL hello ${host:-(eager host)}"; echo "$out"; fail=1; fi
done
for f in cat echo cat-debug; do
  out=$($exe examples/wasip3-rust/dist/$f.wasm 2>&1 | tail -3 | tr '\n' ' ')
  echo "info $f (eager host, empty stdin): $out"
done
exit $fail
