#!/usr/bin/env bash
# Write the trust dump (`silmaril.trust-dump.v0.1`) that `sil project sqlite --trust PATH` reads.
#
#   scripts/trust-export.sh [-o PATH] [MODULE …]
#
# The modules (default: the trust and bytes examples) are imported by a generated driver file,
# which runs `#trust_export` (Silmaril.Prelude.Trust.Export). The dump covers every `Silmaril`
# module those imports reach. Modules that are not imported are not covered: a missing dump,
# or a module absent from it, means unknown, not clean. Run under a profile with
# scripts/trust-profile.sh first if the dump should describe that profile's build.
set -euo pipefail
cd "$(dirname "$0")/.."
out=.lake/silmaril/trust.json
if [ "${1:-}" = "-o" ]; then out=$2; shift 2; fi
if [ $# -eq 0 ]; then
  set -- Silmaril.Prelude.Trust.Examples Silmaril.Prelude.Bytes.Examples \
    Silmaril.Data.IncludeBytes.KernelExamples Silmaril.Data.IncludeBytes.KernelImportExamples
fi
${LAKE:-lake} build "$@" Silmaril.Prelude.Trust.Export.Defs >/dev/null
driver=$(mktemp --suffix=.lean)
trap 'rm -f "$driver"' EXIT
{
  for m in "$@"; do echo "import $m"; done
  echo "import Silmaril.Prelude.Trust.Export.Defs"
  echo "#trust_export \"$out\""
} > "$driver"
${LAKE:-lake} env lean "$driver"
