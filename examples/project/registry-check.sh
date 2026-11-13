#!/usr/bin/env bash
# The `sil project` steps that need no Lean, on silmaril's own project; CI runs them whenever a
# file they read changes (.github/paths-filter.yml, `project`), and selftest.sh runs them first:
#
#   init     in a scratch directory (writes silmaril.toml, the registry and a records file)
#   lock     on the committed registry: must change nothing
#   lint     the records files and the registry
#
#   SIL=build/bin/silmaril-project examples/project/registry-check.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
sil=${SIL:-$root/build/bin/silmaril-project}
[ -x "$sil" ] || { echo "registry-check: $sil is not built; run 'make project-tool'" >&2; exit 2; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
step() { printf '== sil project %s\n' "$*"; }

step "init (a scratch project)"
mkdir "$tmp/scratch"
printf 'name = "scratch"\n' > "$tmp/scratch/lakefile.toml"
"$sil" init --dir "$tmp/scratch"
for f in silmaril.toml silmaril/artifacts.toml silmaril/records.toml; do
  [ -f "$tmp/scratch/$f" ] || { echo "registry-check: init did not write $f" >&2; exit 1; }
done
"$sil" lint --dir "$tmp/scratch"

cd "$root"
step "lock (the committed registry)"
cp silmaril/artifacts.toml "$tmp/artifacts.toml"
"$sil" lock
if ! cmp -s "$tmp/artifacts.toml" silmaril/artifacts.toml; then
  diff -u "$tmp/artifacts.toml" silmaril/artifacts.toml || true
  echo "registry-check: silmaril/artifacts.toml was not locked; commit the file lock wrote" >&2
  exit 1
fi

step lint
"$sil" lint

