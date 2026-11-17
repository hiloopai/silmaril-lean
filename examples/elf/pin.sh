#!/usr/bin/env bash
# The pinned ELF files of the ELF reader examples (examples/elf/README.md).
#   examples/elf/pin.sh --check   the committed files have the pinned sha256
#   examples/elf/pin.sh --fetch   download the package, verify it, extract the file
set -euo pipefail
cd "$(dirname "$0")"
DEB_URL=https://launchpad.net/ubuntu/+archive/primary/+files/coreutils_9.4-3ubuntu6.3_amd64.deb
DEB_URL_MIRROR=http://archive.ubuntu.com/ubuntu/pool/main/c/coreutils/coreutils_9.4-3ubuntu6.3_amd64.deb
DEB_SHA=e1e9a17892be0cc83b7cea747edf331ffeb6d6c010b4db296e60d888e8e9274c
SHA256SUM_SHA=4d2db56c867e5324e0084c9e897f6360d37517de77ac96f2bd31494223d69a60
check() { echo "$2  $1" | sha256sum --check --quiet; }
# glibc 2.39 (libc.so.6, libm.so.6) and zlib (libz.so.1.3), Ubuntu 24.04 amd64: the files of the
# explorer's function tables (examples/elf/README.md). Each line: name, package URL, package sha256,
# member, file sha256.
LIBS=(
  "glibc-libc.so.6 https://launchpad.net/ubuntu/+archive/primary/+files/libc6_2.39-0ubuntu8.9_amd64.deb ff5557d99b51f761c4b7c92368b9cc45565eda17df9bf9eb4b134d09825008be ./usr/lib/x86_64-linux-gnu/libc.so.6 3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf"
  "glibc-libm.so.6 https://launchpad.net/ubuntu/+archive/primary/+files/libc6_2.39-0ubuntu8.9_amd64.deb ff5557d99b51f761c4b7c92368b9cc45565eda17df9bf9eb4b134d09825008be ./usr/lib/x86_64-linux-gnu/libm.so.6 fce00b6f25f459cf4ae0b7fae4257909a1a8a86f9149e7c029a5d617baf1ccd0"
  "zlib-libz.so.1.3 https://launchpad.net/ubuntu/+archive/primary/+files/zlib1g_1.3.dfsg-3.1ubuntu2.3_amd64.deb 376249c8de139568221dbb242318cc8cb8f02299e3a62b7432948e1754fbddf9 ./usr/lib/x86_64-linux-gnu/libz.so.1.3 f61677c7bdb7c2aa2a243ea781bfd16afcb361cede7b4ef76127a9d8eb9a5242"
  "zlib-libz.so.1.2.11 https://launchpad.net/ubuntu/+archive/primary/+files/zlib1g_1.2.11.dfsg-2ubuntu9.2_amd64.deb 9dc17e51a1be2d9ed63b7b84ef0e4e29c5abe6f1bc62cb03e7181483cce8a2f2 ./lib/x86_64-linux-gnu/libz.so.1.2.11 64c206f0146cc58bbddc4f22054436f4ff278f5a554aa3ce6921ddf7e9133370"
)
fetch_member() {  # fetch_member NAME URL DEB_SHA MEMBER FILE_SHA
  local tmp; tmp=$(mktemp -d)
  curl -fsSL -o "$tmp/p.deb" "$2"
  check "$tmp/p.deb" "$3"
  if command -v dpkg-deb >/dev/null; then dpkg-deb --fsys-tarfile "$tmp/p.deb" > "$tmp/data.tar"
  else (cd "$tmp" && ar x p.deb data.tar.zst && zstd -q -d data.tar.zst -o data.tar); fi
  mkdir "$tmp/x" && tar -xf "$tmp/data.tar" -C "$tmp/x" "$4"
  check "$tmp/x/$4" "$5"
  install -m 0644 "$tmp/x/$4" "pinned/$1"
  rm -rf "$tmp"
  echo "pin.sh: wrote pinned/$1"
}
case "${1:-}" in
  --check)
    check pinned/gnu-sha256sum "$SHA256SUM_SHA"
    for l in "${LIBS[@]}"; do set -- $l; check "pinned/$1" "$5"; done
    check ../elf-ladder/01-leaf-arith/pinned/leaf-arith d9cf1e5ddd99bcb2abeca7ae44f899c03bbd93586458a7367e1ff6d4a6472484
    check ../elf-ladder/03-zlib-checksums/pinned/zlib-checksums eeb7934b8c5a13b6fb98ee1a3a15dd2e6861436a6502544dcc549695c39df343
    (cd ../libs/zlib/pinned && sha256sum --check --quiet SHA256SUMS)
    for h in hello-gcc hello-clang; do check "../dyn/pinned/$h" "$(awk -v h="$h" '$1 == h {print $2}' ../dyn/pins.txt)"; done
    echo "pin.sh: ok" ;;
  --fetch)
    tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
    curl -fsSL -o "$tmp/coreutils.deb" "$DEB_URL" || curl -fsSL -o "$tmp/coreutils.deb" "$DEB_URL_MIRROR"
    check "$tmp/coreutils.deb" "$DEB_SHA"
    mkdir "$tmp/x"
    if command -v dpkg-deb >/dev/null; then dpkg-deb --fsys-tarfile "$tmp/coreutils.deb" > "$tmp/data.tar"
    else (cd "$tmp" && ar x coreutils.deb data.tar.zst && zstd -q -d data.tar.zst -o data.tar); fi
    tar -xf "$tmp/data.tar" -C "$tmp/x" ./usr/bin/sha256sum
    check "$tmp/x/usr/bin/sha256sum" "$SHA256SUM_SHA"
    install -m 0644 "$tmp/x/usr/bin/sha256sum" pinned/gnu-sha256sum
    echo "pin.sh: wrote pinned/gnu-sha256sum"
    for l in "${LIBS[@]}"; do fetch_member $l; done ;;
  *) echo "usage: $0 --check | --fetch" >&2; exit 2 ;;
esac
