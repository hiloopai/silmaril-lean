#!/usr/bin/env bash
# Install the pinned tools of tools/wasm-jco/tests/pins.sh into $SIL_TOOLS
# (default ~/.cache/silmaril-tools). Downloads go to a fresh empty directory and are checked
# against the pinned SHA-256 before anything is copied; nothing inside an archive is run.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
. "$here/pins.sh"

check() { [[ $(sha256sum "$1" | cut -d' ' -f1) == "$2" ]] || { echo "SHA-256 mismatch: $1" >&2; exit 1; }; }

dl=$(mktemp -d /tmp/wasm-jco-dl-XXXXXX)
trap 'rm -rf "$dl"' EXIT

if [[ ! -f $WASM_TOOLS ]]; then
  mkdir "$dl/wt" && curl -sSfL -o "$dl/wt/a.tar.gz" "$WASM_TOOLS_URL"
  check "$dl/wt/a.tar.gz" "$WASM_TOOLS_ARCHIVE_SHA256"
  tar -xzf "$dl/wt/a.tar.gz" -C "$dl/wt"
  check "$dl/wt/wasm-tools-$WASM_TOOLS_VERSION-x86_64-linux/wasm-tools" "$WASM_TOOLS_SHA256"
  mkdir -p "$(dirname "$WASM_TOOLS")" && cp "$dl/wt/wasm-tools-$WASM_TOOLS_VERSION-x86_64-linux/wasm-tools" "$WASM_TOOLS"
fi
if [[ ! -f $WASMTIME ]]; then
  mkdir "$dl/wm" && curl -sSfL -o "$dl/wm/a.tar.xz" "$WASMTIME_URL"
  check "$dl/wm/a.tar.xz" "$WASMTIME_ARCHIVE_SHA256"
  tar -xJf "$dl/wm/a.tar.xz" -C "$dl/wm"
  check "$dl/wm/wasmtime-v$WASMTIME_VERSION-x86_64-linux/wasmtime" "$WASMTIME_SHA256"
  mkdir -p "$(dirname "$WASMTIME")" && cp "$dl/wm/wasmtime-v$WASMTIME_VERSION-x86_64-linux/wasmtime" "$WASMTIME"
fi
if [[ ! -f $WAC ]]; then
  mkdir "$dl/wac" && curl -sSfL -o "$dl/wac/wac" "$WAC_URL"
  check "$dl/wac/wac" "$WAC_SHA256"
  mkdir -p "$(dirname "$WAC")" && install -m 755 "$dl/wac/wac" "$WAC"
fi
if [[ ! -f $JCO_JS ]] && command -v npm >/dev/null; then
  mkdir "$dl/jco" && (cd "$dl/jco" && npm pack --silent "@bytecodealliance/jco@$JCO_VERSION" >/dev/null)
  check "$dl/jco/bytecodealliance-jco-$JCO_VERSION.tgz" "$JCO_TGZ_SHA256"
  mkdir -p "$JCO_DIR"
  (cd "$JCO_DIR" && npm install --silent --ignore-scripts --no-audit --no-fund "$dl/jco/bytecodealliance-jco-$JCO_VERSION.tgz")
fi
if [[ ! -f $WIT_BINDGEN ]]; then
  mkdir "$dl/wb" && curl -sSfL -o "$dl/wb/a.tar.gz" "$WIT_BINDGEN_URL"
  check "$dl/wb/a.tar.gz" "$WIT_BINDGEN_ARCHIVE_SHA256"
  tar -xzf "$dl/wb/a.tar.gz" -C "$dl/wb"
  check "$dl/wb/wit-bindgen-$WIT_BINDGEN_VERSION-x86_64-linux/wit-bindgen" "$WIT_BINDGEN_SHA256"
  mkdir -p "$(dirname "$WIT_BINDGEN")" && install -m 755 "$dl/wb/wit-bindgen-$WIT_BINDGEN_VERSION-x86_64-linux/wit-bindgen" "$WIT_BINDGEN"
fi
for k in command reactor proxy; do
  f=$WASI_ADAPTER_DIR/wasi_snapshot_preview1.$k.wasm
  if [[ ! -f $f ]]; then
    mkdir -p "$dl/ad" && curl -sSfL -o "$dl/ad/$k.wasm" \
      "https://github.com/bytecodealliance/wasmtime/releases/download/v$WASMTIME_VERSION/wasi_snapshot_preview1.$k.wasm"
    var=WASI_ADAPTER_${k^^}_SHA256
    check "$dl/ad/$k.wasm" "${!var}"
    mkdir -p "$WASI_ADAPTER_DIR" && cp "$dl/ad/$k.wasm" "$f"
  fi
done
if [[ ! -x $WASI_SDK/bin/clang ]]; then
  mkdir "$dl/sdk" && curl -sSfL -o "$dl/sdk/a.tar.gz" "$WASI_SDK_URL"
  check "$dl/sdk/a.tar.gz" "$WASI_SDK_ARCHIVE_SHA256"
  mkdir -p "$WASI_SDK" && tar -xzf "$dl/sdk/a.tar.gz" -C "$WASI_SDK" --strip-components=1
  check "$WASI_SDK/bin/clang-20" "$WASI_SDK_CLANG_SHA256"
fi
if [[ ! -d $WIT_COMPONENT_TESTS ]]; then
  mkdir "$dl/src" && curl -sSfL -o "$dl/src/a.tar.gz" "$WASM_TOOLS_SRC_URL"
  check "$dl/src/a.tar.gz" "$WASM_TOOLS_SRC_SHA256"
  mkdir -p "$(dirname "$WASM_TOOLS_SRC")"
  tar -xzf "$dl/src/a.tar.gz" -C "$(dirname "$WASM_TOOLS_SRC")" --wildcards \
    'wasm-tools-1.262.0/crates/wit-component/tests/*' 'wasm-tools-1.262.0/LICENSE*'
fi
# The Rust toolchain of the corpus (RUST_HOME) is installed with rustup-init 1.29.2 as described
# in docs/projects/wasm-components.md ("jco"); this script does not install it.
chmod +x "$WASM_TOOLS" "$WASMTIME" "$WAC"
echo "installed under $SIL_TOOLS"
