#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
revision=$(git rev-parse --verify "${1:?provide the commit of the checked database examples}^{commit}")
out=${2:?provide an output directory}
tool=tools/verification-projects/named-logic
git diff --exit-code "$revision" -- Silmaril/ProofFormats/DaslSyntax Silmaril/Proofs/ProofFormats/DaslSyntax
mkdir -p "$out"
lake build --wfail +Silmaril.ProofFormats.DaslSyntax.Database.Examples.Thms
lake env lean -DwarningAsError=true --run "$tool/Export.lean" "$revision" > "$out/named-logic-plan.json"
python3 -BEs "$tool/manifest.py" build "$out/named-logic-plan.json" "$out/named-logic.json"
python3 -BEs "$tool/manifest.py" verify "$out/named-logic-plan.json" "$out/named-logic.json"
python3 -BEs "$tool/test_manifest.py" "$out/named-logic-plan.json"
sha256sum "$out/named-logic-plan.json" "$out/named-logic.json" > "$out/named-logic-sha256.txt"
