#!/usr/bin/env bash
# Build under a trust profile (Silmaril.Prelude.Trust) in its own build directory.
#
#   scripts/trust-profile.sh paranoid Silmaril.Prelude.Bytes.Examples
#   scripts/trust-profile.sh paranoid   # every module except scripts/trust-profile-exclude.txt
#
# The profile is the Lean option `silmaril.trust.profile`, set for every module through
# `[leanOptions]` (as `weak.`, so modules that do not import the option still build), together
# with the ceiling `silmaril.trust.ceiling`, which a source file cannot raise. The option
# is part of each module's trace, and the build directory is `.lake/build-trust-<profile>`, so
# profiles never share or overwrite each other's artifacts. The statements proved are the same in
# every profile; `trust_audit` and `#print axioms` show which proofs ran native code.
set -euo pipefail
cd "$(dirname "$0")/.."
profile=${1:?usage: scripts/trust-profile.sh <default|local|paranoid|SET> [lake build args…]}
shift
case $profile in (*[!A-Za-z0-9_.]*) echo "bad profile name: $profile" >&2; exit 2;; esac
config="lakefile.trust-$profile.toml"
trap 'rm -f "$config"' EXIT
python3 -I - "$profile" "$config" <<'PY'
import sys
profile, out = sys.argv[1], sys.argv[2]
text = open("lakefile.toml").read()
head, sep, rest = text.partition("[leanOptions]\n")
if not sep:
    raise SystemExit("lakefile.toml has no [leanOptions] table")
head = f'buildDir = ".lake/build-trust-{profile}"\n' + head
rest = (f'weak.silmaril.trust.profile = "{profile}"\n'
        f'weak.silmaril.trust.ceiling = "{profile}"\n' + rest)
open(out, "w").write(head + sep + rest)
PY
if [ $# -eq 0 ]; then
  # Every library module except the explicit exclusions (modules that demonstrate native runs
  # of procedures without a kernel fallback, or test one profile's messages).
  mapfile -t targets < <(python3 -I - "$profile" <<'PY'
import pathlib, sys
excl = set()
for line in open("scripts/trust-profile-exclude.txt"):
    line = line.split("#")[0].strip()
    if line and line.split()[0] in (sys.argv[1], "*"):
        excl.add(line.split()[1])
for p in sorted(pathlib.Path("Silmaril").rglob("*.lean")):
    m = ".".join(p.with_suffix("").parts)
    if m not in excl and ".SpecTec" not in m:
        print(m)
PY
)
  set -- "${targets[@]}"
  excluded=$(grep -cE "^($profile|\*) " scripts/trust-profile-exclude.txt || true)
  if [ "$excluded" -gt 0 ]; then
    echo "trust coverage: PARTIAL. $excluded module(s) excluded under profile $profile" \
      "(scripts/trust-profile-exclude.txt); this build is not a full $profile audit." >&2
    grep -E "^($profile|\*) " scripts/trust-profile-exclude.txt | sed 's/^/  excluded: /' >&2
  fi
fi
${LAKE:-lake} -f "$config" build --wfail "$@"
if [ "${excluded:-0}" -gt 0 ]; then
  echo "trust coverage: PARTIAL ($excluded excluded); passed for the modules built, not a full $profile audit." >&2
fi
