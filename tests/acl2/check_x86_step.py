#!/usr/bin/env python3
"""Reject an order-changing mutation that preserves the direct call graph."""

from hashlib import sha256
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/acl2-x86isa"))
from check_step import CORPUS, check, generate


def main():
    manifest_bytes = (CORPUS / "manifest.json").read_bytes()
    body = json.loads((CORPUS / "step-body.json").read_bytes())
    # Swap the outer translated lambda's two formals, leaving its actuals in place.
    body["body"][0][1].reverse()
    modified = (json.dumps(body, separators=(",", ":")) + "\n").encode("utf-8")
    manifest = json.loads(manifest_bytes)
    manifest["step_body_sha256"] = sha256(modified).hexdigest()
    check(manifest, modified)
    try:
        generate(manifest_bytes, modified)
    except ValueError as error:
        if str(error) == "step body differs from the pin":
            print("Rejected an altered lambda formal order with unchanged call dependencies")
            return
        raise
    raise AssertionError("accepted an altered lambda formal order")


if __name__ == "__main__":
    main()
