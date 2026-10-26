#!/usr/bin/env bash
# Differential test: apps/sha256-cli/build/sha256 vs coreutils sha256sum, on a
# corpus covering the empty string, "abc", and the 55/56/63/64/65-byte MD
# padding boundaries plus a 1 MiB random input. Each case checks both the exact
# 65-byte output and the exit status, and that nothing is written to stderr.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
bin="$here/../build/sha256"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
fail=0
check() {
  local name="$1" file="$2"
  local want got rc
  want="$(sha256sum < "$file" | cut -d' ' -f1)"
  "$bin" < "$file" 2>"$tmp/err" >"$tmp/out" && rc=0 || rc=$?
  printf '%s\n' "$want" > "$tmp/want"
  got="$(cat "$tmp/out")"
  if ! cmp -s "$tmp/out" "$tmp/want" || [ "$rc" != 0 ] || [ -s "$tmp/err" ]; then
    echo "FAIL $name: rc=$rc want=$want got=$got stderr=$(cat "$tmp/err")"
    fail=1
  else
    echo "ok   $name ($(wc -c <"$file") bytes) $got"
  fi
}
printf '' > "$tmp/empty"; check empty "$tmp/empty"
printf 'abc' > "$tmp/abc"; check abc "$tmp/abc"
for n in 1 55 56 57 63 64 65 119 120 128 1000; do
  head -c "$n" /dev/zero | tr '\0' 'a' > "$tmp/z$n"; check "len$n" "$tmp/z$n"
done
head -c 1048576 /dev/urandom > "$tmp/rand"; check rand1M "$tmp/rand"
# a pipe (bash-script style): cat | sha256
printf 'hello\nworld\n' | "$bin" > "$tmp/pout" && diff <(printf 'hello\nworld\n' | sha256sum | cut -d' ' -f1) "$tmp/pout" && echo "ok   pipe"
exit $fail
