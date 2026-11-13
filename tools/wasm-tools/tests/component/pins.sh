# Pinned reference tool of the `wasm-tools component …` differential tests (sourced by the
# scripts of this directory). The upstream binary is called by its absolute path only, never
# through PATH, so that it cannot be confused with the Lean `wasm-tools`.
#
# wasm-tools 1.262.0 (2026-10-13), the GitHub release asset
#   https://github.com/bytecodealliance/wasm-tools/releases/download/v1.262.0/wasm-tools-1.262.0-x86_64-linux.tar.gz
#   archive SHA-256 655b8df67d54c3ef9b52fc237c4e94bbfbb5f5f43825245cb0940a7002a9ed65
# installed by tools/wasm-jco/tests/install.sh into ~/.cache/silmaril-tools/wasm-tools-1.262.0/.
SIL_TOOLS=${SIL_TOOLS:-$HOME/.cache/silmaril-tools}
WT_UPSTREAM="$SIL_TOOLS/wasm-tools-1.262.0/wasm-tools"
WT_UPSTREAM_SHA256="fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211"

# Skip (exit 0) when the pinned binary is absent; fail when it is not the pinned one.
wtc_require_upstream() {
  if [[ ! -x $WT_UPSTREAM ]]; then
    echo "SKIP: pinned wasm-tools 1.262.0 not installed at $WT_UPSTREAM"; exit 0
  fi
  local got; got=$(sha256sum "$WT_UPSTREAM" | cut -d' ' -f1)
  if [[ $got != "$WT_UPSTREAM_SHA256" ]]; then
    echo "FAIL: $WT_UPSTREAM has SHA-256 $got, want $WT_UPSTREAM_SHA256"; exit 1
  fi
}
