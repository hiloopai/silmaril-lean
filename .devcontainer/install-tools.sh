#!/bin/sh
set -eu

case "$(uname -m)" in
  x86_64)
    arch=x86_64
    node_arch=x64
    node_sha=2642f4428869aca32443660fd71b3918e2be1277a899bdcaeb64c93b54b5af17
    elan_sha=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
    binaryen_sha=2dc9c7813f5375db93d96ead4b78222fcc3e2677bbb832297af4797782a37489
    wasmtime_sha=0107351ed1f2c141c4069b110cff5fdb937d73cdcb29e3ecf66ed967717fdf5a
    ;;
  aarch64)
    arch=aarch64
    node_arch=arm64
    node_sha=07f0558316ebb8977dd6fb29b4de8d369a639d3d8cef544293852a6f5eea6af8
    elan_sha=05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9
    binaryen_sha=89c07ea56faf38d0fbecf36ca8ec0721756716185f265b568e133d427f299bf8
    wasmtime_sha=9f3e64e56bd579974354e37f4087d42d3b2a594980bca84d09e0c515ba80e45f
    ;;
  *) echo "Unsupported container architecture: $(uname -m)" >&2; exit 1 ;;
esac

# Check the downloaded bytes against the release asset hashes before extraction.
fetch() {
  curl --fail --location --retry 3 "$1" --output "$2"
  printf '%s  %s\n' "$3" "$2" | sha256sum --check --status
}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
cd "$tmp"
case "${1:-}" in
  base)
    fetch "https://nodejs.org/dist/v24.10.0/node-v24.10.0-linux-$node_arch.tar.xz" node.tar.xz "$node_sha"
    tar -xJf node.tar.xz --strip-components=1 -C /usr/local
    fetch "https://github.com/leanprover/elan/releases/download/v4.2.4/elan-$arch-unknown-linux-gnu.tar.gz" elan.tar.gz "$elan_sha"
    tar -xzf elan.tar.gz
    install -m 755 elan-init /usr/local/bin/elan-init
    ;;
  cross-test)
    fetch "https://github.com/WebAssembly/binaryen/releases/download/version_133/binaryen-version_133-$arch-linux.tar.gz" binaryen.tar.gz "$binaryen_sha"
    mkdir -p /opt/binaryen
    tar -xzf binaryen.tar.gz --strip-components=1 -C /opt/binaryen
    fetch "https://github.com/bytecodealliance/wasmtime/releases/download/v37.0.3/wasmtime-v37.0.3-$arch-linux.tar.xz" wasmtime.tar.xz "$wasmtime_sha"
    mkdir -p /opt/wasmtime
    tar -xJf wasmtime.tar.xz --strip-components=1 -C /opt/wasmtime
    ;;
  *) echo "Usage: $0 base|cross-test" >&2; exit 1 ;;
esac
