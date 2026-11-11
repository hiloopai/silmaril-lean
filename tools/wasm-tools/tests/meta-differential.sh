#!/usr/bin/env bash
# Differential test of the meta subcommands (demangle, metadata show, metadata add) of our
# Lean wasm-tools against the pinned upstream wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/meta-differential.sh [--ours BIN] [--keep DIR]
#
# Every case runs the same arguments through both binaries (upstream by its absolute path, never
# via PATH) and compares the exit code, stdout (or the -o output file) byte for byte, and stderr
# (exactly for usage errors, by class -- non-empty, starting with "error:" -- otherwise).
# Skips (exit 0) with a message when the pinned binary is absent. Exit 1 if any case differs.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
# shellcheck source=pins.sh
source "$here/pins.sh"
WT=$WT_UPSTREAM
OURS=$root/.lake/build/bin/wasm-tools
KEEP=
while [[ $# -gt 0 ]]; do
  case $1 in
    --ours) OURS=$2; shift 2 ;;
    --keep) KEEP=$2; shift 2 ;;
    *) echo "usage: $0 [--ours BIN] [--keep DIR]" >&2; exit 2 ;;
  esac
done
wt_require_upstream
wt_require_ours "$OURS" wasm-tools
unset COLUMNS
d=${KEEP:-$(mktemp -d)}
mkdir -p "$d/in" "$d/run"
pass=0; fail=0; failures=()

# ---- corpus -------------------------------------------------------------------------------
# The vendored corpus (its WIT packages and WASI 0.3 components), the fetched WASI adapters and,
# when $WT_CAT_DEBUG is set, the large debug component.
wt_corpus_check
for f in "$WT_CORPUS_DIR"/{cat,echo,hello,demo,wasi-*}.wasm $(wt_adapters) $(wt_cat_debug); do
  [[ -f $f ]] && cp "$f" "$d/in/$(basename "$f")"
done
# Synthetic inputs, written as WAT and converted by upstream `parse`.
wat() { printf '%s\n' "$2" > "$d/in/$1.wat"; "$WT" parse "$d/in/$1.wat" -o "$d/in/$1.wasm" && rm "$d/in/$1.wat"; }
wat names-rust '(module (func $do_no_demangle_me) (func $_ZN4rustE) (func $_Z3food)
  (func $_ZN3foo3bar17h05af221e174051e9E) (func $_RNvCs1234_7mycrate3foo)
  (func $_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17h4ea7d6e3a8b0dbb3E)
  (func $_RINvNtCs9ltgdHTiPiY_4core3ptr13drop_in_placeNtCs1GqpiK2gzZl_5alloc6StringEB4_)
  (func $_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h8c6a2a1e0bd8c9e2E.llvm.123ABC)
  (func $_RNvMs_NtCs4fqI2P2rA04_7mycrate3fooNtB4_3Foo3new) (func $main) (func $i) (func $v)
  (func (param i32) (local $_ZN1a1bE i32)))'
wat names-cpp '(module (func $_Z3foov) (func $_Z3fooi) (func $_ZN2ns3fooEPKc) (func $_Z1fRKSt6vectorIiSaIiEE)
  (func $_ZNK3Foo3getEv) (func $_ZN3FooC2Ev) (func $_ZN3FooD1Ev) (func $_Z5printIiEvT_)
  (func $_ZplRK1AS1_) (func $_ZN9__gnu_cxx13new_allocatorIcE8allocateEmPKv) (func $_Z1fPFviE)
  (func $_Z1fA3_i) (func $_Z1fM1AFviE) (func $_ZSt4cout) (func $_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backERKi)
  (func $_GLOBAL__sub_I_a.cpp) (func $_Z1fIJidEEvDpT_) (func $c) (func $Dn) (func $3foo))'
wat named-module '(module $my-module (func $f) (@producers (language "Rust" "") (processed-by "rustc" "1.0")))'
wat named-component '(component $my-name (core module $submodule) (core module (@name "another submodule")))'
wat oci '(module (@custom "authors" "J. Random Hacker") (@custom "description" "a module")
  (@custom "version" "1.2.3") (@custom "revision" "abc123") (@custom "licenses" "Apache-2.0 WITH LLVM-exception OR MIT")
  (@custom "homepage" "https://Example.com:443/a/./b/../c") (@custom "source" "https://github.com/x/y"))'
wat bad-license '(module (@custom "licenses" "Foo-1.0"))'
wat bad-utf8-free '(module (@custom "authors" "\ff"))'
wat empty-module '(module)'
wat empty-component '(component)'
wat long-names '(component $a-very-long-component-name-that-will-not-fit-in-the-table (core module $another-long-module-name-for-wrapping-the-columns (@producers (language "Rust" "") (language "C" "") (processed-by "clang" "18.1.2 (https://github.com/llvm/llvm-project 26a1d6601d727a96f4301d0d8647b5a42760ae0c)"))))'
# `.dep-v0` sections (cargo-auditable dependency lists): valid and malformed zlib/JSON.
python3 -I "$here/depv0-cases.py" "$d/in"
for f in "$d"/in/dep-*.wat; do "$WT" parse "$f" -o "${f%.wat}.wasm" && rm "$f"; done
printf '\0asm\1\0\0\0\1\5' > "$d/in/truncated.wasm"
printf 'not wasm at all' > "$d/in/text.wasm"
printf '\0asm\x0d\0\1\0\1\x08\0asm\2\0\0\0' > "$d/in/bad-nested.wasm"

# ---- running -------------------------------------------------------------------------------
# run NAME EXACT_STDERR ARGS...   (ARGS may contain @OUT, replaced by a per-binary output path)
run() {
  local name=$1 exact=$2; shift 2
  local a=() b=() x
  for x in "$@"; do a+=("${x//@OUT/$d/run/up.out}"); b+=("${x//@OUT/$d/run/our.out}"); done
  rm -f "$d/run/up.out" "$d/run/our.out"
  "$WT" "${a[@]}" > "$d/run/up.stdout" 2> "$d/run/up.stderr" < /dev/null; local ru=$?
  "$OURS" "${b[@]}" > "$d/run/our.stdout" 2> "$d/run/our.stderr" < /dev/null; local ro=$?
  local why=
  [[ $ru == "$ro" ]] || why="exit $ru vs $ro"
  [[ -z $why ]] && ! cmp -s "$d/run/up.stdout" "$d/run/our.stdout" && why="stdout differs"
  if [[ -z $why && -f $d/run/up.out ]]; then cmp -s "$d/run/up.out" "$d/run/our.out" || why="output file differs"; fi
  if [[ -z $why && $exact == exact ]]; then cmp -s "$d/run/up.stderr" "$d/run/our.stderr" || why="stderr differs"; fi
  if [[ -z $why && $ru != 0 && $exact != exact ]]; then
    head -c 6 "$d/run/our.stderr" | grep -q '^error' || why="stderr class (ours: $(head -c 60 "$d/run/our.stderr"))"
  fi
  if [[ -z $why ]]; then pass=$((pass+1)); else fail=$((fail+1)); failures+=("$name: $why"); fi
}

for f in "$d"/in/*.wasm; do
  n=$(basename "$f")
  run "demangle $n" class demangle "$f" -o @OUT
  run "metadata show $n" class metadata show "$f"
  run "metadata show --json $n" class metadata show --json "$f"
  run "metadata add --name $n" class metadata add --name foo "$f" -o @OUT
  run "metadata add producers $n" class metadata add --language Lean=4 --processed-by tool=1 --sdk s=2 --processed-by rustc=9 "$f" -o @OUT
  run "metadata add oci $n" class metadata add --authors me --description d --version 1 --revision r --licenses MIT --homepage https://a.example/x "$f" -o @OUT
  run "metadata add clear $n" class metadata add --clear-name --clear-authors --clear-description --clear-version --clear-revision --clear-licenses --clear-homepage --clear-source "$f" -o @OUT
done

# Command-line behaviour (exact stderr).
for c in "demangle" "metadata show" "metadata add" "metadata"; do
  run "$c -h" exact $c -h
  run "$c --help" exact $c --help
done
run "metadata help show" exact metadata help show
run "metadata help add" exact metadata help add
run "metadata help help" exact metadata help help
run "metadata (no command)" exact metadata
run "unknown flag" exact demangle --foo
run "two inputs" exact demangle a b
run "repeated flag" exact demangle -t -t
run "repeated option" exact metadata add --name a --name b
run "bad color" exact demangle --color foo
run "missing value" exact demangle -o
run "missing value before flag" exact metadata add --output -t
run "flag with value" exact metadata add --wat=1
run "conflict" exact metadata add --clear-name --name a
run "conflict -g" exact metadata add -g --generate-dwarf lines
run "bad key=value" exact metadata add --language foo
run "bad dwarf" exact metadata add --generate-dwarf foo
run "unknown short in cluster" exact metadata add -tq
# clap's suggestions ("a similar argument exists") and the usage line of used arguments.
while IFS= read -r line; do
  read -ra argv <<< "$line"
  run "suggest: $line" exact "${argv[@]}"
done <<'EOS'
demangle --outptu x
demangle --wa
demangle -o x -t --outptu
demangle -t -o x --verbos
demangle -t -v -v --verbos
demangle --outptu=3
demangle -t --output --foo
demangle -t --output --outpt
demangle -t -o --wt
demangle -t --color=never --verbos=3
demangle -t --hlp
demangle in.wasm --wt
demangle -o x in.wasm --outptu
demangle --colour never
demangle --wat --waat
metadata show --jsn
metadata show -o a --js
metadata add --nme x
metadata add --clear-nam
metadata add --name a --sdk a=1 --langage
metadata add -g --nme
metadata add --processed x
metadata add --language a=1 --language b=2 --x
metadata add --generate-dwar
metadata add --licence MIT
metadata add --clear-sdk
metadata add -o x in.wasm --clear-name --name a
metadata add -v -v --clear-name --name a
metadata shw
metadata ad
metadata hlp
metadata --hlp
metadata -x
metadata --x=3
EOS
run "missing file" exact demangle /nonexistent/x.wasm
run "directory input" exact metadata show /

# Demangler corpus: symbol lists (one per line) in tools/wasm-tools/tests/symbols/*.txt and,
# when the pinned wasi-sdk 27 is installed, the symbols of its libc++ and libc++abi. Each list
# becomes a module whose function names are the symbols; both demanglers run on it and the
# names are compared one by one (reported per list; any difference fails the case).
corpus() {
  local list=$1 tag=$2
  python3 -I "$here/symbols.py" wat "$list" "$d/run/$tag.wat"
  "$WT" parse "$d/run/$tag.wat" -o "$d/run/$tag.wasm" || { fail=$((fail+1)); failures+=("corpus $tag: parse"); return; }
  "$WT" demangle "$d/run/$tag.wasm" -o "$d/run/$tag.up.wasm"
  "$OURS" demangle "$d/run/$tag.wasm" -o "$d/run/$tag.our.wasm"
  python3 -I "$here/symbols.py" names "$d/run/$tag.up.wasm" > "$d/run/$tag.up.txt"
  python3 -I "$here/symbols.py" names "$d/run/$tag.our.wasm" > "$d/run/$tag.our.txt"
  local total same kept diff
  total=$(wc -l < "$list")
  paste "$list" "$d/run/$tag.up.txt" "$d/run/$tag.our.txt" > "$d/run/$tag.cmp"
  same=$(awk -F'\t' '$2==$3' "$d/run/$tag.cmp" | wc -l)
  kept=$(awk -F'\t' '$2!=$3 && $1==$3' "$d/run/$tag.cmp" | wc -l)
  diff=$(awk -F'\t' '$2!=$3 && $1!=$3' "$d/run/$tag.cmp" | wc -l)
  echo "corpus $tag: $total symbols, $same identical, $kept left mangled where upstream demangles, $diff demangled differently"
  if [[ $same == "$total" ]]; then pass=$((pass+1)); else fail=$((fail+1)); failures+=("corpus $tag: $kept kept, $diff different"); fi
}
for l in "$here"/symbols/*.txt; do [[ -f $l ]] && corpus "$l" "$(basename "$l" .txt)"; done
# Mutants of the C++ corpora (20000, seed 1: truncations, deletions, insertions, replacements of
# one character). Most are not valid symbols; both demanglers must agree on which they accept
# and on the text, except for the symbols listed in symbols-mutants-known.txt (documented in
# tools/wasm-tools/README.md).
python3 -I "$here/symbols-mutate.py" 20000 1 "$here"/symbols/cpp-*.txt "$here/symbols/handpicked.txt" \
  > "$d/run/mutants.txt"
python3 -I "$here/symbols.py" wat "$d/run/mutants.txt" "$d/run/mutants.wat"
"$WT" parse "$d/run/mutants.wat" -o "$d/run/mutants.wasm"
"$WT" demangle "$d/run/mutants.wasm" -o "$d/run/mutants.up.wasm"
"$OURS" demangle "$d/run/mutants.wasm" -o "$d/run/mutants.our.wasm"
python3 -I "$here/symbols.py" names "$d/run/mutants.up.wasm" > "$d/run/mutants.up.txt"
python3 -I "$here/symbols.py" names "$d/run/mutants.our.wasm" > "$d/run/mutants.our.txt"
paste "$d/run/mutants.txt" "$d/run/mutants.up.txt" "$d/run/mutants.our.txt" \
  | awk -F'\t' '$2!=$3 {print $1}' > "$d/run/mutants.diff"
unknown=$(grep -vxFf "$here/symbols-mutants-known.txt" "$d/run/mutants.diff" | wc -l)
echo "corpus mutants: 20000 symbols, $(wc -l < "$d/run/mutants.diff") different ($unknown not in symbols-mutants-known.txt)"
if [[ $unknown == 0 ]]; then pass=$((pass+1)); else fail=$((fail+1)); failures+=("corpus mutants: $unknown unexpected differences"); fi
SDK=$WASI_SDK
if [[ -x $SDK/bin/llvm-nm ]]; then
  "$SDK/bin/llvm-nm" -j "$SDK/share/wasi-sysroot/lib/wasm32-wasip1/libc++.a" \
    "$SDK/share/wasi-sysroot/lib/wasm32-wasip1/libc++abi.a" 2>/dev/null | grep -v ':$' | grep -v '^$' | sort -u > "$d/run/libcxx.txt"
  corpus "$d/run/libcxx.txt" libcxx
fi

echo "meta-differential: $pass passed, $fail failed (corpus: $(ls "$d/in" | wc -l) inputs, work dir $d)"
for x in "${failures[@]}"; do echo "  FAIL $x"; done
[[ -z $KEEP ]] && rm -rf "$d"
[[ $fail == 0 ]]
