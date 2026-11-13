# Pinned external tools of the wasm-jco test suite (sourced by run.sh and install.sh).
#
# Each tool lives in $SIL_TOOLS/<tool>-<version>/ (default ~/.cache/silmaril-tools), never in
# the repository or system-wide. The SHA-256 sums below were recorded on 2026-11-09 from the
# GitHub release assets (archives) and the binaries they contain; install.sh checks both.
# All four releases are at least two weeks older than that date.

SIL_TOOLS=${SIL_TOOLS:-$HOME/.cache/silmaril-tools}

# wasm-tools 1.262.0 (2026-10-13): validate, print, component embed/new/wit
WASM_TOOLS_VERSION=1.262.0
WASM_TOOLS_URL=https://github.com/bytecodealliance/wasm-tools/releases/download/v1.262.0/wasm-tools-1.262.0-x86_64-linux.tar.gz
WASM_TOOLS_ARCHIVE_SHA256=655b8df67d54c3ef9b52fc237c4e94bbfbb5f5f43825245cb0940a7002a9ed65
WASM_TOOLS_SHA256=fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211
WASM_TOOLS=$SIL_TOOLS/wasm-tools-$WASM_TOOLS_VERSION/wasm-tools

# wasmtime 50.0.0 (2026-10-20). Streams need the component-model async features:
#   wasmtime run -W component-model-async=y,component-model-async-stackful=y --invoke 'f(…)' C.wasm
WASMTIME_VERSION=50.0.0
WASMTIME_URL=https://github.com/bytecodealliance/wasmtime/releases/download/v50.0.0/wasmtime-v50.0.0-x86_64-linux.tar.xz
WASMTIME_ARCHIVE_SHA256=77c19ee0437991f9ac7837b9c269d9c7076744f85dad263fea5214cc2723c7ff
WASMTIME_SHA256=f95e5beba6d176b447c2939607bae968ea47f87b156ddf559762f1bb3c00e9b7
WASMTIME=$SIL_TOOLS/wasmtime-$WASMTIME_VERSION/wasmtime

# wac 0.12.0 (2026-09-30): `wac plug` to compose test components (the release asset is the binary)
WAC_VERSION=0.12.0
WAC_URL=https://github.com/bytecodealliance/wac/releases/download/v0.12.0/wac-cli-x86_64-unknown-linux-musl
WAC_SHA256=7cd490edbd452221ef89e6750fc43eacc9b71b1242095eb577cb9a3bf0d3beda
WAC=$SIL_TOOLS/wac-$WAC_VERSION/wac

# jco 1.39.0 (2026-10-16), npm, installed with --ignore-scripts and run with node.
# `npm pack @bytecodealliance/jco@1.39.0` gives the tarball below; npm's registry integrity is
# sha512-SiedCAjpkiI+AfK8nEdxqBi7EXbnpW17cASJ3TnRAW+87hltspp4PfMqBAsvQFjt7ePYyuwN8j4F/OBQe4ASmA==
JCO_VERSION=1.39.0
JCO_TGZ_SHA256=ec31290d87207f526ef86509db5351b10edf90b36ce27cc8f0a34130b09f60a5
JCO_DIR=$SIL_TOOLS/jco-$JCO_VERSION
JCO_JS=$JCO_DIR/node_modules/@bytecodealliance/jco/dist/jco.js
# dist/jco.js of that tarball
JCO_JS_SHA256=d21349cf2c04e2ccac5ae4863ca983965637790de52039eca32cdbc79c6aefc9

# `have_tool NAME PATH SHA256`: 0 if PATH exists with that SHA-256; 1 (with a message) if it is
# absent; exits 1 if it exists with another sum.
have_tool() {
  if [[ ! -x $2 && ! -f $2 ]]; then
    echo "skip: $1 not installed at $2 (tools/wasm-jco/tests/install.sh installs it)"
    return 1
  fi
  local got
  got=$(sha256sum "$2" | cut -d' ' -f1)
  if [[ $got != "$3" ]]; then
    echo "error: $2 has SHA-256 $got, pinned $3" >&2
    exit 1
  fi
}

# --- Real-producer corpus (tools/wasm-jco/tests/corpus) -------------------------------------
# wit-bindgen CLI 0.62.0 (2026-09-10), the released binary of
# https://github.com/bytecodealliance/wit-bindgen/releases/download/v0.62.0/wit-bindgen-0.62.0-x86_64-linux.tar.gz
WIT_BINDGEN_VERSION=0.62.0
WIT_BINDGEN_URL=https://github.com/bytecodealliance/wit-bindgen/releases/download/v0.62.0/wit-bindgen-0.62.0-x86_64-linux.tar.gz
WIT_BINDGEN_ARCHIVE_SHA256=3e81cc6523729f7532b4aa7968648a04abf0c711b7d1677150e9121f4e6458fe
WIT_BINDGEN_SHA256=aefa50fcbbced25862d2b7c65c3b44b63e63302d8e2533f1aeeab6e8cff4ff72
WIT_BINDGEN=$SIL_TOOLS/wit-bindgen-$WIT_BINDGEN_VERSION/wit-bindgen

# Rust 1.99.1 (58cf8f9c3 2026-10-13) with the wasm32-wasip2 standard library, installed by
# rustup-init 1.29.2 into $SIL_TOOLS/rust-1.99.1/{rustup,cargo} (see
# docs/projects/wasm-components.md, "jco"; rustup checks every component against the
# channel manifest `channel-rust-1.99.1.toml`, SHA-256
# fb152be80975c194aa5fc684b2aec3a6e14e2b855efe2faa4e5f8ae6e590f463). Its linker
# wasm-component-ld 0.5.27 has SHA-256 below; `-Clink-arg=--skip-wit-component` makes it write
# the core module (with its component-type sections) instead of a component.
RUST_VERSION=1.99.1
RUST_HOME=$SIL_TOOLS/rust-$RUST_VERSION
RUST_TOOLCHAIN=$RUST_HOME/rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu
RUSTC_ID='rustc 1.99.1 (58cf8f9c3 2026-10-13)'
WASM_COMPONENT_LD_SHA256=394fad5b002e16eac8cead786ce083049e569785e72d4bc8b2eddfd21b389d85
# Crates (exact versions and checksums in corpus/rust/Cargo.lock) are fetched into their own
# CARGO_HOME, never the user's:
CORPUS_CARGO_HOME=$SIL_TOOLS/jco-corpus-cargo

# The official WASI preview 1 adapters of wasmtime 50.0.0 (release assets of v50.0.0).
WASI_ADAPTER_DIR=$SIL_TOOLS/wasi-adapter-50.0.0
WASI_ADAPTER_COMMAND_SHA256=b3de00ac47528237211c6404b4a7e4235a67878665dc3e8853071908c3127a85
WASI_ADAPTER_REACTOR_SHA256=73b01f85e42e99c890efbbf619cd765e04e5809da36d976b87fc64abd87f5812
WASI_ADAPTER_PROXY_SHA256=0b7918e6bfb9a9da9fda9a9518c8964d8ef06f688be488d3a5377c7e63e1ac95
WASI_ADAPTER_COMMAND=$WASI_ADAPTER_DIR/wasi_snapshot_preview1.command.wasm
WASI_ADAPTER_REACTOR=$WASI_ADAPTER_DIR/wasi_snapshot_preview1.reactor.wasm
WASI_ADAPTER_PROXY=$WASI_ADAPTER_DIR/wasi_snapshot_preview1.proxy.wasm
# (The adapter's source is vendored in vendor/wasi/adapter, at wasmtime v50.0.1; the binaries
# above are the v50.0.0 release assets. tools/wasm-jco/tests/adapt.sh uses them.)
# The Rust wasm32-wasip1 standard library (for adapt.sh's preview 1 corpus) is added to RUST_HOME
# by `rustup target add --toolchain 1.99.1-x86_64-unknown-linux-gnu wasm32-wasip1` (rustup checks
# it against the channel manifest above); manifest-rust-std-wasm32-wasip1 lists its files.

# wasi-sdk 27 (2025), the released x86_64-linux archive, for the C programs of adapt.sh's preview 1
# corpus (corpus/p1/*.c): clang 20.1.8-wasi-sdk, wasi-libc for wasm32-wasip1. Extracted with
# --strip-components=1 into $WASI_SDK; nothing in it is run but bin/clang (and the linker it calls).
WASI_SDK_VERSION=27.0
WASI_SDK_URL=https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-27/wasi-sdk-27.0-x86_64-linux.tar.gz
WASI_SDK_ARCHIVE_SHA256=b7d4d944c88503e4f21d84af07ac293e3440b1b6210bfd7fe78e0afd92c23bc2
WASI_SDK=$SIL_TOOLS/wasi-sdk-$WASI_SDK_VERSION
WASI_SDK_CLANG_SHA256=e78c818b321d834a20df5796afa9a9329dc53fd1f0a2597166c7a283b355be77

# wasm-tools 1.262.0 source (the GitHub tag archive), for the wit-component test corpus
# crates/wit-component/tests/components (tools/wasm-jco/tests/wit-component.sh). Only the test
# inputs (.wat/.wit/.txt) and the licences are extracted; nothing in it is run.
WASM_TOOLS_SRC_URL=https://github.com/bytecodealliance/wasm-tools/archive/refs/tags/v1.262.0.tar.gz
WASM_TOOLS_SRC_SHA256=8fafe356b7c63e396d6869c41cb78f76104ae342e1543734f10058d4d5df101c
WASM_TOOLS_SRC=$SIL_TOOLS/wasm-tools-src-1.262.0/wasm-tools-1.262.0
WIT_COMPONENT_TESTS=$WASM_TOOLS_SRC/crates/wit-component/tests/components
