#!/usr/bin/env python3
"""Read the pinned pure Bitops world and evaluate logical observations in ACL2."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
TOOLS = HERE.parents[2] / "tools/acl2-x86isa"
sys.path.insert(0, str(TOOLS))
from export_x86_run import TREE
from inventory import COMMIT, digest, lisp_string


BOOK = "centaur/bitops/part-select"
INPUTS = (f"books/{BOOK}.lisp", "books/ihs/basic-definitions.lisp", "axioms.lisp")


def export(checkout, output, *, book=BOOK, inputs=INPUTS, samples="bit-selection-samples.lsp",
           metadata="bit-selection-world.lsp", driver="export-bit-selection"):
    checkout = checkout.resolve()
    commit, tree = subprocess.check_output(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"], cwd=checkout, text=True,
    ).splitlines()
    if (commit, tree) != (COMMIT, TREE) or subprocess.run(
        ["git", "diff", "--quiet", "HEAD", "--"], cwd=checkout,
    ).returncode:
        raise ValueError(f"use the clean ACL2 8.7 checkout at {COMMIT}, tree {TREE}")
    source = checkout / inputs[0]
    acl2 = checkout / "saved_acl2"
    if not acl2.is_file() or not source.with_suffix(".cert").is_file():
        raise ValueError(f"build saved_acl2 with SBCL and certify {book} first")
    env = {**os.environ, "ACL2_CUSTOMIZATION": "NONE", "ACL2_SYSTEM_BOOKS": str(checkout / "books"),
           "X86ISA_EXEC": "nil", "LC_ALL": "C"}
    log = output.with_suffix(output.suffix + ".log")
    with tempfile.TemporaryDirectory(prefix="acl2-logical-world-") as directory:
        staging = Path(directory) / "world.json"
        commands = (
            "(set-ld-error-action '(:exit 1) state)\n"
            f'(include-book "{book}" :dir :system :ttags nil :uncertified-okp nil '
            ':defaxioms-okp nil :skip-proofs-okp nil)\n'
            + (HERE / samples).read_text(encoding="utf-8")
            + ":q\n(handler-case (progn\n"
            f'  (load {lisp_string(TOOLS / "certificate.lisp")})\n'
            f'  (load {lisp_string(TOOLS / "x86-run.lisp")})\n'
            f'  (load {lisp_string(HERE / metadata)})\n'
            f'  ({driver} {lisp_string(source)} {lisp_string(staging)}) (sb-ext:exit :code 0))\n'
            '  (error (condition) (format *error-output* "~a~%" condition) (sb-ext:exit :code 1)))\n'
        )
        with log.open("w", encoding="utf-8") as transcript:
            result = subprocess.run([acl2], input=commands, text=True, cwd=checkout, env=env,
                                    stdout=transcript, stderr=subprocess.STDOUT)
        if result.returncode or not staging.is_file():
            raise ValueError(f"ACL2 export did not complete. See {log}")
        definitions, observations = json.loads(staging.read_bytes())
    fields = {
        "schema": 1, "acl2_commit": commit, "acl2_tree": tree,
        "source_sha256": {path: digest(checkout / path) for path in inputs},
    }
    # Keep each public source row and observation on one line for review.
    lines = [f"  {json.dumps(key)}: {json.dumps(value)}" for key, value in fields.items()]
    for key, rows in [("definitions", definitions), ("observations", observations)]:
        lines.append(f'  "{key}": [\n    ' + ",\n    ".join(map(json.dumps, rows)) + "\n  ]")
    output.write_text("{\n" + ",\n".join(lines) + "\n}\n", encoding="utf-8")
    print(f"{digest(output)}  {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    try:
        export(args.checkout, args.output)
    except ValueError as error:
        parser.exit(1, f"{error}\n")
