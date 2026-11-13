#!/usr/bin/env bash
# Check CLI binaries against the decidable specifications of Silmaril.Cli.Io.Examples with the
# harness `cli-harness` (docs/projects/wasm-binaryen-tooling.md):
#   * cli-io-demo {echo,cat,copy}: the Lean programs that echo_sat/cat_sat/copy_sat are about,
#     run with Prog.toIO;
#   * the pinned Rust WASI 0.3 components examples/wasip3-rust/dist/{echo,cat}.wasm, run by
#     wasmtime 50.0.0 (`run -S p3 -W component-model-async`), SHA-256
#     f95e5beba6d176b447c2939607bae968ea47f87b156ddf559762f1bb3c00e9b7;
#   * a negative control: the echo suite must reject /bin/cat.
# Needs the Lean executables: lake build cli-harness cli-io-demo. Each step prints SKIP
# when what it needs is absent, so CI without the tools is unaffected.
set -uo pipefail
root=$(cd "$(dirname "$0")/../../.." && pwd)
bin=$root/.lake/build/bin
TOOLS=${SIL_TOOLS:-$HOME/.cache/silmaril-tools}
WM=$TOOLS/wasmtime-50.0.0/wasmtime
WM_SHA=f95e5beba6d176b447c2939607bae968ea47f87b156ddf559762f1bb3c00e9b7
H=$bin/cli-harness
fail=0
if [[ ! -x $H || ! -x $bin/cli-io-demo ]]; then
  echo "SKIP: cli-harness/cli-io-demo not built (lake build cli-harness cli-io-demo)"
  exit 0
fi
for s in echo cat copy echon; do
  "$H" "$s" -- "$bin/cli-io-demo" "$s" || fail=1
done
if "$H" echo -- /bin/cat >/dev/null; then
  echo "FAIL: the echo suite accepted /bin/cat"; fail=1
else
  echo "ok: the echo suite rejects /bin/cat"
fi
if [[ -x $WM ]] && echo "$WM_SHA  $WM" | sha256sum -c --quiet; then
  dist=$root/examples/wasip3-rust/dist
  "$H" echo -- "$WM" run -S p3 -W component-model-async "$dist/echo.wasm" || fail=1
  "$H" cat -- "$WM" run -S p3 -W component-model-async "$dist/cat.wasm" || fail=1
else
  echo "SKIP: wasmtime 50.0.0 absent or not the pinned binary ($WM)"
fi
[[ $fail == 0 ]] && echo "all ok" || echo "FAILURES"
exit $fail
