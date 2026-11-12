#!/usr/bin/env bash
# Performance of the gentool subcommands against pinned wasm-tools 1.262.0, on KB to
# multi-MB inputs. Prints a table (seconds, best of 3) and fails when ours is slower than
# `GT_BENCH_FACTOR` (default 10) times upstream plus 0.5 s: a regression test.
#
#   tools/wasm-tools/tests/gen/bench.sh
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/pins.sh"
gt_require_upstream
gt_ours
factor=${GT_BENCH_FACTOR:-10}
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
cd "$work"
U=$GT_UPSTREAM; O=$GT_OURS

best() {  # best wall time of 3 runs of "$@", in seconds
  local b=999999 t
  for _ in 1 2 3; do
    local s; s=$(date +%s.%N)
    "$@" >/dev/null 2>&1
    t=$(echo "$(date +%s.%N) - $s" | bc)
    b=$(echo "if ($t < $b) $t else $b" | bc)
  done
  printf '%.3f' "$b"
}

fail=0
row() {  # name input-size ours upstream
  local verdict=ok
  if (( $(echo "$3 > $factor * $4 + 0.5" | bc) )); then verdict=SLOW; fail=1; fi
  printf '| %-28s | %10s | %8s | %8s | %s |\n' "$1" "$2" "$3" "$4" "$verdict"
}

echo "| case                         |      input |  ours s | upstr s | verdict |"
echo "|------------------------------|------------|---------|---------|---------|"
# smith: seeds of 1 KB to 4 MB
for n in 1024 65536 1048576 4194304; do
  head -c $n /dev/urandom > seed-$n
  row "smith (seed)" "$n B" "$(best "$O" smith seed-$n -o o.wasm)" "$(best "$U" smith seed-$n -o u.wasm)"
done
# wit-smith (genapi track): seeds of 1 KB to 4 MB, with and without `-t`
for n in 1024 1048576 4194304; do
  row "wit-smith (seed)" "$n B" "$(best "$O" wit-smith seed-$n -o o.wasm)" \
    "$(best "$U" wit-smith seed-$n -o u.wasm)"
  row "wit-smith -t (seed)" "$n B" "$(best "$O" wit-smith -t seed-$n -o o.wat)" \
    "$(best "$U" wit-smith -t seed-$n -o u.wat)"
done
# inputs for mutate (core modules of the repository, 52 KB to 3 MB): the WASI adapter, and the
# core module of examples/wasip3-rust/dist/cat-debug.wasm (unbundled by upstream), with and
# without its custom sections (DWARF)
root=$(cd "$here/../../../.." && pwd)
cp "$root/examples/wasm-components/adapter/wasi_snapshot_preview1.command.wasm" in-adapter.wasm
mkdir -p ub
"$U" component unbundle "$root/examples/wasip3-rust/dist/cat-debug.wasm" --module-dir ub \
  -o ub/rest.wasm
cp ub/unbundled-module0.wasm in-catdebug.wasm
"$U" strip in-catdebug.wasm -o in-catdebug-stripped.wasm
for f in in-adapter.wasm in-catdebug-stripped.wasm in-catdebug.wasm; do
  sz=$(stat -c %s "$f")
  for s in 1 2; do
    row "mutate -s $s" "$sz B" "$(best "$O" mutate "$f" -s $s -o m.wasm)" \
      "$(best "$U" mutate "$f" -s $s -o m.wasm)"
  done
  row "mutate --preserve-semantics" "$sz B" \
    "$(best "$O" mutate "$f" -s 1 --preserve-semantics -o m.wasm)" \
    "$(best "$U" mutate "$f" -s 1 --preserve-semantics -o m.wasm)"
done
# mutate on text input: upstream's print of a generated module (silmaril's certified WAT
# reader is the cost). The module avoids GC and exceptions, which the certified text
# elaborator does not read.
"$O" smith seed-65536 --min-funcs 8 --gc-enabled false --exceptions-enabled false \
  -o tx.wasm; "$U" print tx.wasm > in-text.wat
sz=$(stat -c %s in-text.wat)
row "mutate -s 1 (text input)" "$sz B" "$(best "$O" mutate in-text.wat -s 1 -o m.wasm)" \
  "$(best "$U" mutate in-text.wat -s 1 -o m.wasm)"
# The 1.9 MB text of the stripped cat-debug core module: one run, informational (not in the
# budget). 35.6 s; 2.2 s (linear-time lexer `WatLex.lexF`, 0.6 s; elaborator
# `WatFast.moduleF?` with a per-function identifier check linear in the locals, 1.0 s, against
# 16 s for silmaril's `module?`).
"$U" print in-catdebug-stripped.wasm > in-cat.wat
sz=$(stat -c %s in-cat.wat)
s0=$(date +%s.%N); "$O" mutate in-cat.wat -s 1 -o m.wasm >/dev/null 2>&1
t=$(echo "$(date +%s.%N) - $s0" | bc)
s0=$(date +%s.%N); "$U" mutate in-cat.wat -s 1 -o m.wasm >/dev/null 2>&1
tu=$(echo "$(date +%s.%N) - $s0" | bc)
printf '| %-28s | %10s | %8.3f | %8.3f | %s |\n' "mutate -s 1 (cat-debug text)" "$sz B" "$t" "$tu" info
# smith with the widened options
row "smith (4 mems/tables, customs)" "65536 B" \
  "$(best "$O" smith seed-65536 --max-memories 4 --max-tables 4 --generate-custom-sections true -o o.wasm)" \
  "$(best "$U" smith seed-65536 --max-memories 4 --max-tables 4 --generate-custom-sections true -o u.wasm)"
# smith with the an earlier step features through flags and a JSON configuration
printf '{"max-funcs": 50, "max-instructions": 1000, "min-funcs": 20}' > big.json
row "smith (--config, 20-50 funcs)" "65536 B" "$(best "$O" smith seed-65536 -c big.json -o o.wasm)" \
  "$(best "$U" smith seed-65536 -c big.json -o u.wasm)"
# wit-smith: seeds of 1 KB to 1 MB
for n in 1024 65536 1048576; do
  row "wit-smith (seed)" "$n B" "$(best "$O" wit-smith seed-$n -o w.wasm)" \
    "$(best "$U" wit-smith seed-$n -o w.wasm)"
done
# shrink: keep a module that still has a function (predicate through upstream
# print), 100 attempts
printf '#!/bin/sh\n"%s" print "$1" | grep -q "^  (func"\n' "$U" > pred.sh; chmod +x pred.sh
# The input avoids GC and exceptions: upstream's shrink (wasm-mutate) makes no progress on
# them and writes no output, so there is nothing to compare.
"$O" smith seed-65536 --min-funcs 5 --gc-enabled false --exceptions-enabled false -o sh.wasm
if ./pred.sh sh.wasm; then
  sz=$(stat -c %s sh.wasm)
  row "shrink (script predicate)" "$sz B" "$(best "$O" shrink ./pred.sh sh.wasm -a 100 -o a.wasm)" \
    "$(best "$U" shrink ./pred.sh sh.wasm -a 100 -o b.wasm)"
  printf '  shrunk to: ours %s B, upstream %s B\n' "$(stat -c %s a.wasm)" "$(stat -c %s b.wasm)"
fi
# The same with GC and exceptions on: one run, informational (upstream leaves it unshrunk)
"$O" smith seed-65536 --min-funcs 5 -o shg.wasm
if ./pred.sh shg.wasm; then
  sz=$(stat -c %s shg.wasm); rm -f a.wasm b.wasm
  s0=$(date +%s.%N); "$O" shrink ./pred.sh shg.wasm -a 100 -o a.wasm >/dev/null 2>&1
  t=$(echo "$(date +%s.%N) - $s0" | bc)
  s0=$(date +%s.%N); "$U" shrink ./pred.sh shg.wasm -a 100 -o b.wasm >/dev/null 2>&1
  tu=$(echo "$(date +%s.%N) - $s0" | bc)
  printf '| %-28s | %10s | %8.3f | %8.3f | %s |\n' "shrink (GC, exceptions)" "$sz B" "$t" "$tu" info
  printf '  shrunk to: ours %s B, upstream %s\n' "$(stat -c %s a.wasm 2>/dev/null || echo none)" \
    "$( [[ -e b.wasm ]] && echo "$(stat -c %s b.wasm) B" || echo 'no output')"
fi
[[ $fail == 0 ]]
