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
exit $status
