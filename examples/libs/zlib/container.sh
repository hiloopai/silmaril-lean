#!/usr/bin/env bash
# Runs inside the pinned container (examples/libs/zlib/build.sh starts it): installs the pinned
# toolchain from the Ubuntu snapshot archive, then builds zlib 1.3.1's shared library
# libz.so.1.3.1 from the release tarball with each compiler named on the command line.
#   container.sh OUT CC...    CC is gcc-13 or clang-18; writes OUT/libz.so.1.3.1-CC,
#                             OUT/packages-CC.txt (the installed toolchain) and OUT/build-CC.log
# Inputs (read-only mounts): /in/zlib-1.3.1.tar.gz, checked against its SHA-256 here as well.
set -euo pipefail
out=$1; shift
SNAPSHOT=20261116T000000Z
TARBALL_SHA=9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23
# The toolchain, pinned by version; the snapshot fixes every dependency's version as well.
PKGS=(
  gcc-13=13.3.0-6ubuntu2~24.04.1
  clang-18=1:18.1.3-1ubuntu1
  binutils=2.42-4ubuntu2.10
  libc6-dev=2.39-0ubuntu8.12
  libc6=2.39-0ubuntu8.12
  make=4.3-4.1build2
)
export DEBIAN_FRONTEND=noninteractive
# The snapshot archive is served over HTTPS only and the base image has no CA bundle: install
# ca-certificates from the live archive first. It only lets apt fetch the snapshot's (signed)
# indices; nothing from it reaches the build.
apt-get update -qq
apt-get install -y -qq --no-install-recommends ca-certificates >/dev/null
apt-get update -qq --snapshot "$SNAPSHOT"
apt-get install -y -qq --no-install-recommends --allow-downgrades "${PKGS[@]}" >/dev/null

echo "$TARBALL_SHA  /in/zlib-1.3.1.tar.gz" | sha256sum --check --quiet
# Byte-for-byte reproducibility: a fixed build path, fixed timestamps and locale, and the build
# path mapped away (-ffile-prefix-map; zlib has no __DATE__/__FILE__, so it changes nothing today).
export SOURCE_DATE_EPOCH=1705948320   # 2024-01-22T18:32:00Z, the release's newest tarball mtime
export LC_ALL=C TZ=UTC
umask 022
for cc in "$@"; do
  rm -rf /build && mkdir /build && cd /build
  tar -xzf /in/zlib-1.3.1.tar.gz
  cd /build/zlib-1.3.1
  {
    "$cc" --version | head -1
    ld --version | head -1
    echo "+ CC=$cc CFLAGS='-O2 -ffile-prefix-map=/build/zlib-1.3.1=.' ./configure"
    CC=$cc CFLAGS='-O2 -ffile-prefix-map=/build/zlib-1.3.1=.' ./configure
    echo "+ make libz.so.1.3.1"
    make libz.so.1.3.1
  } > "$out/build-$cc.log" 2>&1 || { cat "$out/build-$cc.log" >&2; exit 1; }
  install -m 0644 libz.so.1.3.1 "$out/libz.so.1.3.1-$cc"
  dpkg-query -W -f '${Package} ${Version}\n' gcc-13 cpp-13 libgcc-13-dev clang-18 libclang-cpp18 \
    libllvm18 binutils binutils-x86-64-linux-gnu libbinutils libc6 libc6-dev libgcc-s1 make \
    > "$out/packages-$cc.txt"
done
