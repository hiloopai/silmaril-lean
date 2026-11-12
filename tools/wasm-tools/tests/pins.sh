# Pinned reference tools and corpora of the wasm-tools tests (sourced by every test script).
#
# This file is the only place that names the tool cache, the pinned versions, their URLs and
# their SHA-256 sums; `fetch-pins.sh` installs them, the test scripts only read them. The
# upstream binaries are called by their absolute paths, never through PATH. Every download is
# treated as data: the archives are checked against the sums below before anything is unpacked,
# and only the released binaries are run.
#
# The cache root is $SIL_TOOLS (default ~/.cache/silmaril-tools); the build command named in the
# "not built" messages is $WT_BUILD_HINT. Both are set here only.

SIL_TOOLS=${SIL_TOOLS:-$HOME/.cache/silmaril-tools}
WT_BUILD_HINT=${WT_BUILD_HINT:-lake build}

# wasm-tools 1.262.0 (2026-10-13), the release binary for x86_64 Linux.
WT_VERSION=1.262.0
WT_URL=https://github.com/bytecodealliance/wasm-tools/releases/download/v1.262.0/wasm-tools-1.262.0-x86_64-linux.tar.gz
WT_ARCHIVE_SHA256=655b8df67d54c3ef9b52fc237c4e94bbfbb5f5f43825245cb0940a7002a9ed65
WT_UPSTREAM_DIR=$SIL_TOOLS/wasm-tools-$WT_VERSION
WT_UPSTREAM=$WT_UPSTREAM_DIR/wasm-tools
WT_UPSTREAM_SHA256=fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211

# The wasm-tools 1.262.0 source (GitHub tag archive, top directory wasm-tools-1.262.0), read as
# data only: tests/cli (dump, missing-features), tests/snapshots/testsuite/**/*.print (the
# printer corpus) and the wasmparser/wasmprinter sources the generators read.
WT_SRC_URL=https://github.com/bytecodealliance/wasm-tools/archive/refs/tags/v1.262.0.tar.gz
WT_SRC_SHA256=8fafe356b7c63e396d6869c41cb78f76104ae342e1543734f10058d4d5df101c
WT_SRC_ARCHIVE=$SIL_TOOLS/dl-wasm-tools-src-full/a.tar.gz
WT_SRC_DIR=$SIL_TOOLS/src/wasm-tools-$WT_VERSION/wasm-tools-$WT_VERSION

# WebAssembly/spec at 608711107b7f1edb13efd57b7d79b49477462d36 (2026-09-22): test/core/**.wast
# (258 files), unpacked to $WASM_SPEC_DIR.
WASM_SPEC_REV=608711107b7f1edb13efd57b7d79b49477462d36
WASM_SPEC_URL=https://codeload.github.com/WebAssembly/spec/tar.gz/$WASM_SPEC_REV
WASM_SPEC_SHA256=22ef0dd9dd9603474c6a58fa644752a3e9b887b4043d5480490290f748acda1b
WASM_SPEC_ARCHIVE=$SIL_TOOLS/dl-wasm-spec-608711107b/spec.tar.gz
WASM_SPEC_DIR=$SIL_TOOLS/src/wasm-spec-608711107b

# Binaryen version_123: `wasm-opt`, the optimizer of the pinned e-graph corpus runs.
BINARYEN_URL=https://github.com/WebAssembly/binaryen/releases/download/version_123/binaryen-version_123-x86_64-linux.tar.gz
BINARYEN_ARCHIVE_SHA256=e959f2170af4c20c552e9de3a0253704d6a9d2766e8fdb88e4d6ac4bae9388fe
BINARYEN_DIR=$SIL_TOOLS/binaryen-123/binaryen-version_123
BINARYEN_WASM_OPT=$BINARYEN_DIR/bin/wasm-opt
BINARYEN_WASM_OPT_SHA256=d66c6724c07334155720eb2def29c434dcaaf741ce859b4f7f389e22674f9c4a

# wasi-sdk 27.0: clang for the DWARF samples of addr2line/, llvm-nm for the demangler corpus.
WASI_SDK_URL=https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-27/wasi-sdk-27.0-x86_64-linux.tar.gz
WASI_SDK_ARCHIVE_SHA256=b7d4d944c88503e4f21d84af07ac293e3440b1b6210bfd7fe78e0afd92c23bc2
WASI_SDK=$SIL_TOOLS/wasi-sdk-27.0
WASI_SDK_CLANG_SHA256=e78c818b321d834a20df5796afa9a9329dc53fd1f0a2597166c7a283b355be77

# The WASI preview1 adapters of wasmtime v50.0.1 (release assets; built from
# crates/wasi-preview1-component-adapter at c307ec81de02852d815e9849f7c89d955c03c30d), core
# modules of about 51 KB in the corpus of the differential suites.
WASI_ADAPTER_URL=https://github.com/bytecodealliance/wasmtime/releases/download/v50.0.1
WASI_ADAPTER_COMMAND_SHA256=0b4fe490390ecc9c2222f969f65b179e658a3327e005efd4ddc959766132a3c4
WASI_ADAPTER_REACTOR_SHA256=6d52112df28f0caee9018f911f279f94f848230b2f0ed02138290363e925671f
WASI_ADAPTER_DIR=$SIL_TOOLS/wasmtime-50.0.1-adapters
WASI_ADAPTER_COMMAND=$WASI_ADAPTER_DIR/wasi_snapshot_preview1.command.wasm
WASI_ADAPTER_REACTOR=$WASI_ADAPTER_DIR/wasi_snapshot_preview1.reactor.wasm

# The debug build of the corpus' cat.wasm (3.1 MB, DWARF 4 with inlining), not vendored: the
# path in $WT_CAT_DEBUG, checked against this SHA-256; the cases that read it are skipped
# when it is unset.
WT_CAT_DEBUG=${WT_CAT_DEBUG:-}
WT_CAT_DEBUG_SHA256=7a8401014533176715777004b61ff1c340db67a131703a6738ff1e0119f91b6c

wt_sha256() { sha256sum "$1" | cut -d' ' -f1; }

# Exit 0 with a SKIP line when the pinned wasm-tools is absent, 1 when it does not match its hash.
wt_require_upstream() {
  if [[ ! -x $WT_UPSTREAM ]]; then
    echo "SKIP: pinned wasm-tools $WT_VERSION not installed at $WT_UPSTREAM (tools/wasm-tools/tests/fetch-pins.sh)"
    exit 0
  fi
  local got; got=$(wt_sha256 "$WT_UPSTREAM")
  if [[ $got != "$WT_UPSTREAM_SHA256" ]]; then
    echo "FAIL: $WT_UPSTREAM has SHA-256 $got, want $WT_UPSTREAM_SHA256" >&2; exit 1
  fi
}

# The source tree, unpacked from the checked archive on first use; SKIP without the archive.
wt_require_src() {
  [[ -d $WT_SRC_DIR ]] && return 0
  if [[ ! -f $WT_SRC_ARCHIVE ]]; then
    echo "SKIP: wasm-tools $WT_VERSION source archive not at $WT_SRC_ARCHIVE (tools/wasm-tools/tests/fetch-pins.sh)"
    exit 0
  fi
  local got; got=$(wt_sha256 "$WT_SRC_ARCHIVE")
  [[ $got == "$WT_SRC_SHA256" ]] || { echo "FAIL: source archive SHA-256 $got" >&2; exit 1; }
  mkdir -p "$(dirname "$WT_SRC_DIR")"
  tar xzf "$WT_SRC_ARCHIVE" -C "$(dirname "$WT_SRC_DIR")"
}

# Our binary: SKIP (exit 0) with the build hint when it is not built. $1 the path, $2 the target.
wt_require_ours() {
  [[ -x $1 ]] && return 0
  echo "SKIP: $1 not built ($WT_BUILD_HINT $2)"
  exit 0
}

# The vendored corpus (tools/wasm-tools/tests/corpus), checked against its SHA256SUMS.
WT_CORPUS_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/corpus
wt_corpus_check() {
  (cd "$WT_CORPUS_DIR" && sha256sum --quiet -c SHA256SUMS) ||
    { echo "FAIL: the vendored corpus does not match $WT_CORPUS_DIR/SHA256SUMS" >&2; exit 1; }
}

# The binaries of the differential corpus, one path per line: the vendored corpus, the test
# fixtures, the adapters when fetched, and the binaries of the wave-1 tools' own tests.
wt_corpus_wasm() {
  local tools; tools=$(cd "$WT_CORPUS_DIR/../../.." && pwd)
  wt_corpus_check
  {
    find "$WT_CORPUS_DIR" "$tools/wasm-tools/tests/fixtures" -maxdepth 1 -name '*.wasm'
    for d in "$tools/wasm-check/tests/inputs" "$tools/wasm-egraph/corpus"; do
      [[ -d $d ]] && find "$d" -name '*.wasm'
    done
    wt_adapters
  } | sort
}

# The adapters, one path per line, when fetched (checked against their SHA-256); none otherwise.
wt_adapters() {
  local f sha
  for f in "$WASI_ADAPTER_COMMAND:$WASI_ADAPTER_COMMAND_SHA256" \
           "$WASI_ADAPTER_REACTOR:$WASI_ADAPTER_REACTOR_SHA256"; do
    sha=${f##*:}; f=${f%:*}
    [[ -f $f ]] || continue
    [[ $(wt_sha256 "$f") == "$sha" ]] || { echo "FAIL: $f does not match its SHA-256" >&2; exit 1; }
    printf '%s\n' "$f"
  done
}

# The large debug component: its path when $WT_CAT_DEBUG is set (checked), empty otherwise.
wt_cat_debug() {
  [[ -n $WT_CAT_DEBUG ]] || return 0
  [[ -f $WT_CAT_DEBUG && $(wt_sha256 "$WT_CAT_DEBUG") == "$WT_CAT_DEBUG_SHA256" ]] ||
    { echo "FAIL: WT_CAT_DEBUG=$WT_CAT_DEBUG is not the pinned cat-debug.wasm" >&2; exit 1; }
  printf '%s\n' "$WT_CAT_DEBUG"
}

# test/core of the pinned spec testsuite (unpacked by fetch-pins.sh spec); empty when absent.
wt_spec_core() {
  local d
  for d in "$WASM_SPEC_DIR"/*/test/core; do [[ -d $d ]] && printf '%s\n' "$d"; done
  return 0
}
