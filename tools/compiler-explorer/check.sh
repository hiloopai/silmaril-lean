#!/usr/bin/env bash
# The compiler explorer, end to end (`make compiler-explorer-check`; CI runs it through `make check`
# whenever `cexplorer-export` or `CompilesToExamples` is in scope):
#   tools/compiler-explorer/check.sh [OUT]          (OUT defaults to .lake/compiler-explorer)
# 1. build the Lean modules and the exporter;
# 2. regenerate the manifests and fail if they differ from the committed ones;
# 3. `verify` every manifest: run the exporter and record its result (fails when a named proof
#    is not evidence: missing, another statement, other axioms);
# 4. fail unless the statuses are examples/compiler-explorer/expected-status.txt;
# 5. replay the kernel on the evidence modules (`replay.sh`, leanchecker);
# The Make target also runs the database and view tests.
# Docker is not needed: the builds and listings are committed (fixtures.py build|listings).
set -euo pipefail
cd "$(dirname "$0")/../.."
LAKE="${LAKE:-lake}"
PYTHON="${PYTHON:-python3}"
out="${1:-.lake/compiler-explorer}"
mkdir -p "$out"
"$LAKE" build --wfail cexplorer-export Silmaril.Compiler.Explorer.Det.Thms \
  Silmaril.Project.Shapes.CompilesTo.Explorer.Thms CompilesToExamples.Explorer.Builds \
  CompilesToExamples.Explorer.Code CompilesToExamples.Explorer.Rows CompilesToExamples.Explorer.Decompiled \
  CompilesToExamples.Explorer.C2C.Runs CompilesToExamples.Explorer.TypeError CompilesToExamples.Explorer.Blocks \
  CompilesToExamples.Explorer.C2C.Elaborates \
  CompilesToExamples.Explorer.Compact.Core \
  Silmaril.Compiler.Explorer.Text.Thms
regen="$(mktemp -d)"
replay_pid=
cleanup() {
  local status=$?
  # Always join the independent replay, including after a foreground failure.
  if [ -n "$replay_pid" ]; then
    if ! wait "$replay_pid"; then status=1; fi
  fi
  rm -rf "$regen"
  trap - EXIT
  exit "$status"
}
trap cleanup EXIT
# Replay reads the completed build; manifest/exporter checks and temporary negative
# fixtures do not modify its oleans. Keep all bounded workers and join their verdict.
LAKE="$LAKE" tools/compiler-explorer/replay.sh &
replay_pid=$!
"$PYTHON" -I tools/compiler-explorer/fixtures.py manifests --out "$regen" > /dev/null
"$PYTHON" -I tools/compiler-explorer/fixtures.py rows --check
"$PYTHON" -I tools/compiler-explorer/fixtures.py stages --check
if ! diff -r "$regen" examples/compiler-explorer/manifests > /dev/null; then
  diff -r "$regen" examples/compiler-explorer/manifests | head -20 >&2
  echo "error: the committed manifests are not what fixtures.py writes" >&2
  exit 1
fi
rm -f "$out/explorer.sqlite"
LAKE="$LAKE" "$PYTHON" -I tools/compiler-explorer/cexplorer.py verify "$out/explorer.sqlite" \
  examples/compiler-explorer/manifests/*.json
"$PYTHON" -I tools/compiler-explorer/cexplorer.py status "$out/explorer.sqlite" > "$out/status.txt"
if ! diff -u examples/compiler-explorer/expected-status.txt "$out/status.txt"; then
  echo "error: the statuses differ from examples/compiler-explorer/expected-status.txt" >&2
  exit 1
fi
"$LAKE" env "$PYTHON" -I tools/compiler-explorer/tests/test_replay.py
wait "$replay_pid"
replay_pid=
echo "compiler explorer: ok ($(grep -c ' proved ' "$out/status.txt") proved obligations)"
