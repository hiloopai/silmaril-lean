# Pinned reference tool for the gentool tests (sourced). Never resolved through PATH: the
# upstream binary is called by its absolute path only.
GT_UPSTREAM_DIR="$HOME/.cache/silmaril-tools/wasm-tools-1.262.0"
GT_UPSTREAM="$GT_UPSTREAM_DIR/wasm-tools"
GT_UPSTREAM_SHA256="fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211"

gt_require_upstream() {
  if [[ ! -x $GT_UPSTREAM ]]; then
    echo "SKIP: pinned wasm-tools 1.262.0 not installed at $GT_UPSTREAM"; exit 0
  fi
  local got; got=$(sha256sum "$GT_UPSTREAM" | cut -d' ' -f1)
  if [[ $got != "$GT_UPSTREAM_SHA256" ]]; then
    echo "FAIL: $GT_UPSTREAM has SHA-256 $got, want $GT_UPSTREAM_SHA256"; exit 1
  fi
}

# Our binary (built by `lake build wasm-tools-gen` or lake), by absolute path.
gt_ours() {
  local root; root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)
  GT_OURS="${WASM_TOOLS_LEAN:-$root/.lake/build/bin/wasm-tools-gen}"
  if [[ ! -x $GT_OURS ]]; then
    echo "SKIP: $GT_OURS not built (lake build wasm-tools-gen)"; exit 0
  fi
}
