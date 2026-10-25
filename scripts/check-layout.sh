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
# from the same region and topic, in the header, Proofs or Raw trees.
violations=$(while IFS= read -r file; do
  mod=${file%.lean}; mod=${mod//\//.}
  topic=$(echo "$mod" | sed -E 's/^Silmaril\.(Proofs\.|Raw\.)?//' | cut -d. -f1-2)
  grep -hoE '^(public )?(meta )?import (all )?Silmaril\.(Proofs|Raw)\.[A-Za-z0-9_.]+' "$file" \
    | awk '{print $NF}' | while IFS= read -r dep; do
      dtopic=$(echo "$dep" | sed -E 's/^Silmaril\.(Proofs|Raw)\.//' | cut -d. -f1-2)
      if [ "$dtopic" != "$topic" ]; then
        echo "$file: imports $dep from another topic; import its Thms header instead" >&2
        echo fail
      fi
    done
done < <(find Silmaril -name '*.lean') || true)
if [ -n "$violations" ]; then status=1; fi
exit $status
