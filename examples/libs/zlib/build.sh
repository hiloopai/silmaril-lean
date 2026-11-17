#!/usr/bin/env bash
# zlib 1.3.1's shared library built from the release tarball by GCC 13 and by Clang 18, in a
# pinned container, byte for byte reproducibly (examples/libs/zlib/README.md).
#   examples/libs/zlib/build.sh           build into examples/libs/zlib/pinned/
#   examples/libs/zlib/build.sh --check   build into a temporary directory and compare
# Needs docker (network: the release tarball and the Ubuntu snapshot archive).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
IMAGE=ubuntu@sha256:73b999393d07f2bf65a40373778a44dc9a6d54ad7718d29247d8ff9413c4d6a8   # ubuntu:24.04
URL=https://github.com/madler/zlib/releases/download/v1.3.1/zlib-1.3.1.tar.gz
SHA256=9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23
in=$(mktemp -d); out=$(mktemp -d); trap 'rm -rf "$in" "$out"' EXIT
curl -fsSL -o "$in/zlib-1.3.1.tar.gz" "$URL"
echo "$SHA256  $in/zlib-1.3.1.tar.gz" | sha256sum --check --quiet
cp "$HERE/container.sh" "$in/"
chmod -R a+rX "$in"; chmod a+rwx "$out"
docker run --rm --network host -v "$in:/in:ro" -v "$out:/out" "$IMAGE" \
  bash /in/container.sh /out gcc-13 clang-18
dest=$HERE/pinned
if [ "${1:-}" = --check ]; then
  for cc in gcc-13 clang-18; do
    cmp "$out/libz.so.1.3.1-$cc" "$dest/libz.so.1.3.1-$cc" && echo "ok libz.so.1.3.1-$cc"
  done
else
  mkdir -p "$dest"
  for cc in gcc-13 clang-18; do
    install -m 0644 "$out/libz.so.1.3.1-$cc" "$out/packages-$cc.txt" "$out/build-$cc.log" "$dest/"
  done
  (cd "$dest" && sha256sum libz.so.1.3.1-gcc-13 libz.so.1.3.1-clang-18 > SHA256SUMS)
  cat "$dest/SHA256SUMS"
fi
