#!/usr/bin/env bash
# Cheap textual layout checks until `sil` takes them over (docs/design.md):
# no `axiom` declarations, no `native_decide`, and no module importing another
# topic's Proofs/Raw tree from outside it.
set -euo pipefail
cd "$(dirname "$0")/.."
status=0
if grep -rnE '^\s*(private |protected )?axiom ' Silmaril --include='*.lean'; then
  echo "error: axiom declarations are not allowed (policy.toml)" >&2; status=1
fi
if grep -rnw 'native_decide' Silmaril --include='*.lean'; then
  echo "error: native_decide is not allowed" >&2; status=1
fi
# Proofs/Raw of topic Silmaril.{Proofs,Raw}.<Region>.<Topic> may be imported only
# from the same region and topic, in the header, Proofs or Raw trees. One awk
# pass over every module: a per-file shell loop took 15 s on CI.
find Silmaril -name '*.lean' -print0 | xargs -0 awk '
  function topic(name,   parts, n) {
    sub(/^Silmaril\.(Proofs\.|Raw\.)?/, "", name)
    n = split(name, parts, ".")
    return n > 1 ? parts[1] "." parts[2] : parts[1]
  }
  FNR == 1 { mod = FILENAME; sub(/\.lean$/, "", mod); gsub("/", ".", mod); own = topic(mod) }
  /^(public )?(meta )?import (all )?Silmaril\.(Proofs|Raw)\.[A-Za-z0-9_.]+/ {
    match($0, /Silmaril\.(Proofs|Raw)\.[A-Za-z0-9_.]+/)
    dep = substr($0, RSTART, RLENGTH)
    if (topic(dep) != own) {
      print FILENAME ": imports " dep " from another topic; import its Thms header instead" > "/dev/stderr"
      bad = 1
    }
  }
  END { exit bad }' || status=1
# Each Silmaril module is matched by the globs of exactly one of `Silmaril` and `SilmarilSpecTec`
# (lakefile.toml lists `Silmaril`'s globs because Lake globs cannot exclude).
python3 -I - <<'PY' || status=1
import pathlib, tomllib
libs = {l["name"]: l["globs"] for l in tomllib.load(open("lakefile.toml", "rb"))["lean_lib"]
        if l["name"] in ("Silmaril", "SilmarilSpecTec")}
def hit(g, m):
    if g.endswith(".*"): return m == g[:-2] or m.startswith(g[:-1])
    if g.endswith(".+"): return m.startswith(g[:-1])
    return m == g
bad = 0
for p in sorted(pathlib.Path("Silmaril").rglob("*.lean")) + [pathlib.Path("Silmaril.lean")]:
    m = ".".join(p.with_suffix("").parts)
    owners = [n for n, gs in libs.items() if any(hit(g, m) for g in gs)]
    if len(owners) != 1:
        print(f"error: {p} is matched by {owners or 'no'} library globs in lakefile.toml", file=__import__("sys").stderr)
        bad = 1
raise SystemExit(bad)
PY
exit $status
