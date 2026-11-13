#!/usr/bin/env bash
# Cheap textual layout checks until `sil` takes them over (docs/design.md):
# no `axiom` declarations, no `native_decide` or `bv_decide`, and no module importing another
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
# Native runs go through `edge_decide` (Silmaril/Prelude/Trust), which consults the trust policy
# and records the procedure. Nothing else calls the native evaluator (backquoted mentions in
# comments are fine). The trust ceiling belongs to the build (scripts/trust-profile.sh).
if grep -rnE 'nativeEqTrue|(^|[^`])decide \+native|decide \(config := \{[^}]*native' Silmaril --include='*.lean' \
    | grep -v '^Silmaril/Prelude/Trust/'; then
  echo "error: native evaluation must go through edge_decide (Silmaril.Prelude.Trust)" >&2; status=1
fi
# Forged test axioms stay in the trust examples, a leaf that nothing imports.
if grep -rnE '^(public )?(meta )?import (all )?Silmaril\.Prelude\.Trust\.(TestForge|Examples)\b' Silmaril --include='*.lean' \
    | grep -v '^Silmaril/Prelude/Trust/Examples.lean:'; then
  echo "error: only Silmaril/Prelude/Trust/Examples.lean may import TestForge, and nothing imports it" >&2; status=1
fi
if grep -rn 'silmaril\.trust\.ceiling' Silmaril --include='*.lean' | grep -v '^Silmaril/Prelude/Trust/'; then
  echo "error: only scripts/trust-profile.sh sets silmaril.trust.ceiling" >&2; status=1
fi
# The trust policy in policy.toml is pinned by Silmaril/Prelude/Trust/Policy/Defs.lean (FNV-1a 64).
python3 -I - <<'PY' || status=1
import re
data = open("policy.toml", "rb").read()
h = 0xcbf29ce484222325
for b in data:
    h = ((h ^ b) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
pin = re.search(r'trust_policy "[^"]*" pin "([0-9a-f]{16})"',
                open("Silmaril/Prelude/Trust/Policy/Defs.lean").read())
if not pin or pin.group(1) != f"{h:016x}":
    print(f"error: policy.toml changed; update the pin in Silmaril/Prelude/Trust/Policy/Defs.lean to {h:016x}",
          file=__import__("sys").stderr)
    raise SystemExit(1)
PY
# `bv_decide` proves goals that need SAT through a native-evaluation axiom
# (`…._native.bv_decide.ax_…`); main uses `bv_decide_kernel`, which fails instead
# (Silmaril/Prelude/BVDecide/Defs.lean, docs/bv-decide-trust.md). Comments,
# strings and code spans are not invocations.
python3 -I - <<'PY' || status=1
import pathlib, re, sys
call = re.compile(r"\bbv_decide(?![\w?'])")
bad = 0
for p in sorted(pathlib.Path("Silmaril").rglob("*.lean")):
    source = p.read_text()
    if "bv_decide" not in source:
        continue
    depth = 0
    for n, line in enumerate(source.splitlines(), 1):
        code, i = [], 0
        while i < len(line):
            if depth == 0 and line.startswith("--", i): break
            if line.startswith("/-", i): depth += 1; i += 2; continue
            if depth and line.startswith("-/", i): depth -= 1; i += 2; continue
            if depth == 0: code.append(line[i])
            i += 1
        text = re.sub(r'"(\\.|[^"\\])*"|`[^`]*`', "", "".join(code))
        if call.search(text):
            print(f"{p}:{n}: bv_decide is not allowed on main; use bv_decide_kernel", file=sys.stderr)
            bad = 1
raise SystemExit(bad)
PY
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
