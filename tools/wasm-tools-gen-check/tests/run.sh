#!/usr/bin/env bash
# Measurements of the verified generator API (docs/projects/wasm-components.md, "track genapi"),
# and an informal cross-check: every generated, mutated and optimised module validates with
# the pinned upstream wasm-tools at the matching feature level.
#
#   lake build wasm-tools-gen-check
#   tools/wasm-tools-gen-check/tests/run.sh [COUNT]
#
# Upstream is called only by absolute path; when it is absent (or its SHA-256 differs) the
# cross-check is skipped with a message and only the Lean-side checks run.
set -euo pipefail
root=$(cd "$(dirname "$0")/../../.." && pwd)
exe="$root/.lake/build/bin/wasm-tools-gen-check"
count=${1:-200}
WT="$HOME/.cache/silmaril-tools/wasm-tools-1.262.0/wasm-tools"
WT_SHA=fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211
[[ -x $exe ]] || { echo "missing $exe: run lake build wasm-tools-gen-check" >&2; exit 2; }
have_wt=0
if [[ -x $WT ]] && [[ $(sha256sum "$WT" | cut -d' ' -f1) == "$WT_SHA" ]]; then
  have_wt=1
else
  echo "SKIP upstream cross-check: pinned wasm-tools 1.262.0 not found at $WT (or SHA-256 differs)"
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0
# feature set : upstream --features
for pair in v10:wasm1 v20:wasm2 v30:wasm3 lime1:wasm3 fx:wasm3,stack-switching; do
  feat=${pair%%:*}; up=${pair#*:}
  out="$tmp/$feat"
  (ulimit -v 8000000; "$exe" --feat "$feat" --count "$count" --size 40 --mutations 5 --out "$out") \
    | sed "s/^/[$feat] /" || { echo "FAIL $feat: checked-output failure"; fail=1; }
  if (( have_wt )); then
    n=0; bad=0
    # `semleft-*` are diagnostics (a stage output that left the feature set, skipped by
    # `optRunIn`), not outputs
    for f in "$out"/gen-*.wasm "$out"/mut-*.wasm "$out"/sem-*.wasm; do
      n=$((n + 1))
      if ! "$WT" validate --features="$up" "$f" 2>"$tmp/err"; then
        bad=$((bad + 1)); echo "[$feat] upstream rejects $(basename "$f"): $(head -1 "$tmp/err")"
      fi
    done
    echo "[$feat] upstream-valid $((n - bad))/$n (--features=$up)"
    (( bad == 0 )) || fail=1
  fi
done
out="$tmp/comp"
(ulimit -v 8000000; "$exe" --component --count "$count" --size 30 --mutations 5 --out "$out") \
  | sed "s/^/[component] /" || { echo "FAIL component"; fail=1; }
if (( have_wt )); then
  n=0; bad=0
  for f in "$out"/*.wasm; do
    n=$((n + 1))
    "$WT" validate "$f" 2>"$tmp/err" || { bad=$((bad + 1)); echo "[component] upstream rejects $(basename "$f"): $(head -1 "$tmp/err")"; }
  done
  echo "[component] upstream-valid $((n - bad))/$n"
  (( bad == 0 )) || fail=1
fi
# the typed generator (valid by construction, `Gen.Typed`): our checker and upstream
for pair in v10:wasm1 v20:wasm2 v30:wasm3 lime1:wasm3; do
  feat=${pair%%:*}; up=${pair#*:}
  out="$tmp/typed-$feat"
  (ulimit -v 8000000; "$exe" --typed --feat "$feat" --count "$count" --size 40 --out "$out") \
    | sed "s/^/[typed $feat] /" || { echo "FAIL typed $feat"; fail=1; }
  if (( have_wt )); then
    n=0; bad=0
    for f in "$out"/*.wasm; do
      n=$((n + 1))
      "$WT" validate --features="$up" "$f" 2>"$tmp/err" || { bad=$((bad + 1)); echo "[typed $feat] upstream rejects $(basename "$f"): $(head -1 "$tmp/err")"; }
    done
    echo "[typed $feat] upstream-valid $((n - bad))/$n (--features=$up)"
    (( bad == 0 )) || fail=1
  fi
done
# the typed Core 3.0 generator (valid by construction, `Gen.Typed3`: GC, exceptions,
# multi-memory, memory64, typed function references), at every S >= v30
for pair in v30:wasm3 fx:wasm3,stack-switching; do
  feat=${pair%%:*}; up=${pair#*:}
  out="$tmp/typed3-$feat"
  (ulimit -v 8000000; "$exe" --typed3 --feat "$feat" --count "$count" --size 40 --out "$out") \
    | sed "s/^/[typed3 $feat] /" || { echo "FAIL typed3 $feat"; fail=1; }
  if (( have_wt )); then
    n=0; bad=0
    for f in "$out"/*.wasm; do
      n=$((n + 1))
      "$WT" validate --features="$up" "$f" 2>"$tmp/err" || { bad=$((bad + 1)); echo "[typed3 $feat] upstream rejects $(basename "$f"): $(head -1 "$tmp/err")"; }
    done
    echo "[typed3 $feat] upstream-valid $((n - bad))/$n (--features=$up)"
    (( bad == 0 )) || fail=1
  fi
done
(ulimit -v 8000000; "$exe" --wit --count "$count" --size 30 --mutations 5) \
  | sed "s/^/[wit] /" || { echo "FAIL wit"; fail=1; }
exit $fail
