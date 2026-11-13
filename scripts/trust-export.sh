#!/usr/bin/env bash
# Write the core trust export (`silmaril.trust-core.v1`). The project database converts it to its
# own `silmaril.trust-dump.v0.1`; that converter and its compatibility belong to the database task.
#
#   scripts/trust-export.sh [--db] [-o PATH] [MODULE …]
#
# With --db it writes the project database's `silmaril.trust-dump.v0.1`
# (docs/projects/trust-db.md) to .lake/silmaril/trust.json instead.
#
# The modules (default: the trust and bytes examples) are imported by a generated driver file,
# which runs `#trust_export` (Silmaril.Prelude.Trust.Export). Modules and uses cover every
# `Silmaril` module those imports reach; `declarations` covers the listed modules. Modules that are not imported are not covered: a missing dump,
# or a module absent from it, means unknown, not clean. Run under a profile with
# scripts/trust-profile.sh first if the dump should describe that profile's build.
set -euo pipefail
cd "$(dirname "$0")/.."
out=""
cmd=trust_export
mod=Silmaril.Prelude.Trust.Export.Defs
if [ "${1:-}" = "--db" ]; then cmd=trust_export_db; mod=Silmaril.Prelude.Trust.ExportDb.Defs; shift; fi
if [ "${1:-}" = "-o" ]; then out=$2; shift 2; fi
if [ -z "$out" ]; then
  if [ $cmd = trust_export_db ]; then out=.lake/silmaril/trust.json; else out=.lake/silmaril/trust-core.json; fi
fi
if [ $# -eq 0 ]; then
  set -- Silmaril.Prelude.Trust.Examples Silmaril.Prelude.Bytes.Examples \
    Silmaril.Data.IncludeBytes.KernelExamples Silmaril.Data.IncludeBytes.KernelImportExamples
fi
${LAKE:-lake} build "$@" "$mod" >/dev/null
driver=$(mktemp --suffix=.lean)
trap 'rm -f "$driver"' EXIT
{
  for m in "$@"; do echo "import $m"; done
  echo "import $mod"
  echo "#$cmd \"$out\" $*"
} > "$driver"
${LAKE:-lake} env lean "$driver"
