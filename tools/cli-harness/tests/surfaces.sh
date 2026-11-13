#!/usr/bin/env bash
# Check the front ends of pinned tools against the behaviour specifications their surfaces give
# (Silmaril.Cli.Io.Surface: Tool.frontSpec, decided by Tool.frontCheck, proved sound by
# Tool.frontCheck_sound), on every vector of the surface's corpus, with `cli-harness surface`
# (docs/projects/wasm-binaryen-tooling.md):
#   * wasm-tools 1.262.0 (pinned: ~/.cache/silmaril-tools/wasm-tools-1.262.0/wasm-tools, SHA-256
#     fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211; tools/wasm-tools/README.md);
#   * wasm-opt, wasm-asyncify, wasm-verify (.lake/build/bin).
# The vectors that fail must be exactly those of tools/cli-harness/tests/surface-known.tsv (tool,
# outcome class, vector; tab-separated); `--update` rewrites it. Each tool is skipped with a
# message when its binary is absent, so CI is unaffected.
# Then the tools behind a clap front end against Clap.Tool.frontSpec (exact derived help and
# usage-error texts and exit codes; Silmaril.Cli.Clap.Main: decided by Clap.Tool.frontCheck, proved
# sound by Clap.Tool.frontCheck_sound) with `cli-harness front`: wasm-asyncify, wasm-jco,
# wasm-wac, and wasm-opt on its help vectors; their failures are recorded as
# `front:TOOL`.
# Needs: lake build cli-harness wasm-opt wasm-asyncify wasm-verify wasm-jco wasm-wac
set -uo pipefail
root=$(cd "$(dirname "$0")/../../.." && pwd)
bin=$root/.lake/build/bin
KNOWN=$root/tools/cli-harness/tests/surface-known.tsv
TOOLS=${SIL_TOOLS:-$HOME/.cache/silmaril-tools}
WT=$TOOLS/wasm-tools-1.262.0/wasm-tools
WT_SHA=fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211
H=$bin/cli-harness
if [[ ! -x $H ]]; then echo "SKIP: cli-harness not built (lake build cli-harness)"; exit 0; fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
: >"$work/found"
run() { # tool cmd
  "$H" surface "$1" -- "$2" >"$work/out" 2>&1
  tail -1 "$work/out"
  sed -n 's/^FAIL: \([^ ]*\) \[\([^]]*\)\] \(.*\): exit .*/\1\t\2\t\3/p' "$work/out" >>"$work/found"
}
if [[ -x $WT ]] && echo "$WT_SHA  $WT" | sha256sum -c --quiet; then run wasm-tools "$WT"
else echo "SKIP: wasm-tools 1.262.0 absent or not the pinned binary ($WT)"; fi
for t in wasm-opt wasm-asyncify wasm-verify; do
  if [[ -x $bin/$t ]]; then run "$t" "$bin/$t"; else echo "SKIP: $bin/$t not built"; fi
done
front() { # tool cmd
  "$H" front "$1" -- "$2" >"$work/out" 2>&1
  tail -1 "$work/out"
  sed -n 's/^FAIL: \([^ ]*\) \[\([^]]*\)\] \(.*\): exit .*/front:\1\t\2\t\3/p' "$work/out" >>"$work/found"
}
for t in wasm-asyncify wasm-jco wasm-wac wasm-opt; do
  if [[ -x $bin/$t ]]; then front "$t" "$bin/$t"; else echo "SKIP: $bin/$t not built"; fi
done
# negative control: a binary that prints nothing fails every non-run vector of a front end
if [[ -x $bin/wasm-jco ]] && "$H" front wasm-jco -- /bin/true >/dev/null 2>&1; then
  echo "FAIL: the wasm-jco front end accepted /bin/true"; exit 1
else echo "ok: the wasm-jco front end rejects /bin/true"; fi
# negative control: /bin/true prints nothing, so it must fail every non-run vector
if [[ -x $WT ]] && "$H" surface wasm-tools -- /bin/true >/dev/null 2>&1; then
  echo "FAIL: the wasm-tools surface accepted /bin/true"; exit 1
else echo "ok: the wasm-tools surface rejects /bin/true"; fi
if [[ ${1:-} == --update ]]; then
  { grep '^#' "$KNOWN"; cat "$work/found"; } >"$work/new"; cp "$work/new" "$KNOWN"
  echo "updated $KNOWN"; exit 0
fi
if diff <(grep -v '^#' "$KNOWN" | sort) <(sort "$work/found") >"$work/diff"; then
  echo "differences: exactly the $(grep -vc '^#' "$KNOWN") pinned in surface-known.tsv"
else
  echo "FAIL: differences changed (< pinned, > found):"; cat "$work/diff"; exit 1
fi
