#!/usr/bin/env bash
# The `sil project` self-test, end to end on silmaril's own project (silmaril.toml, silmaril/,
# examples/project/ProjectSelfTest.lean):
#
#   init     in a scratch directory (writes silmaril.toml, the registry and a records file)
#   lock     on the committed registry: must change nothing
#   lint     the records files and the registry, without Lean
#   dump     lake build --wfail of the project's modules, then #silmaril_dump
#   check    compared with examples/project/check.txt (all but the `sql sha256` line, which
#            follows the toolchain)
#   sqlite   the canonical SQL text and the database, tuned for HTTP reads
#   explore  the static page over the database
#
#   SIL=build/bin/silmaril-project LAKE=lake examples/project/selftest.sh
#   SIL_BLESS=1 examples/project/selftest.sh     # rewrite check.txt; review with git diff
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
sil=${SIL:-$root/build/bin/silmaril-project}
lake=${LAKE:-lake}
[ -x "$sil" ] || { echo "selftest: $sil is not built; run 'make project-tool'" >&2; exit 2; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
step() { printf '== sil project %s\n' "$*"; }

step "init (a scratch project)"
mkdir "$tmp/scratch"
printf 'name = "scratch"\n' > "$tmp/scratch/lakefile.toml"
"$sil" init --dir "$tmp/scratch"
for f in silmaril.toml silmaril/artifacts.toml silmaril/records.toml; do
  [ -f "$tmp/scratch/$f" ] || { echo "selftest: init did not write $f" >&2; exit 1; }
done
"$sil" lint --dir "$tmp/scratch"

cd "$root"
step "lock (the committed registry)"
cp silmaril/artifacts.toml "$tmp/artifacts.toml"
"$sil" lock
if ! cmp -s "$tmp/artifacts.toml" silmaril/artifacts.toml; then
  diff -u "$tmp/artifacts.toml" silmaril/artifacts.toml || true
  echo "selftest: silmaril/artifacts.toml was not locked; commit the file lock wrote" >&2
  exit 1
fi

step lint
"$sil" lint

step dump
"$sil" dump --lake "$lake"

step check
"$sil" check | tee "$tmp/check.txt"
grep -v '^sql sha256: ' "$tmp/check.txt" > "$tmp/check.cmp"
if [ -n "${SIL_BLESS:-}" ]; then
  cp "$tmp/check.cmp" examples/project/check.txt
elif ! diff -u examples/project/check.txt "$tmp/check.cmp"; then
  echo "selftest: the check differs from examples/project/check.txt (SIL_BLESS=1 rewrites it)" >&2
  exit 1
fi

step "sqlite --httpvfs"
"$sil" sqlite --httpvfs > /dev/null
[ -s .lake/silmaril/project.sqlite ] || { echo "selftest: no database" >&2; exit 1; }

step explore
"$sil" explore
grep -q 'project.sqlite' .lake/silmaril/explore.html

echo "selftest: ok"
