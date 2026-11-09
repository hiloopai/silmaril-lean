#!/usr/bin/env bash
# Fetches the zlib 1.3.1 release tarball, checks it, and extracts the files that
# build.sh compiles into zlib-1.3.1/ (checked again by build.sh against
# zlib-1.3.1.sha256). The tarball is the upstream release asset.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
URL=https://github.com/madler/zlib/releases/download/v1.3.1/zlib-1.3.1.tar.gz
SHA256=9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
curl -fsSL -o "$tmp/zlib-1.3.1.tar.gz" "$URL"
echo "$SHA256  $tmp/zlib-1.3.1.tar.gz" | sha256sum -c --quiet
mkdir -p "$HERE/zlib-1.3.1"
tar -xzf "$tmp/zlib-1.3.1.tar.gz" -C "$tmp"
for f in adler32.c crc32.c crc32.h LICENSE zconf.h zlib.h zutil.h; do
  cp "$tmp/zlib-1.3.1/$f" "$HERE/zlib-1.3.1/$f"
done
( cd "$HERE" && sha256sum -c --quiet zlib-1.3.1.sha256 )
