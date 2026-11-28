#!/usr/bin/env python3
"""Export a toy DEFSTOBJ and proved ground observations from pinned stock ACL2."""

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


def export(checkout, output):
    checkout = checkout.resolve()
    commit, tree = subprocess.check_output(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"], cwd=checkout, text=True,
    ).splitlines()
    if (commit, tree) != (COMMIT, TREE) or subprocess.run(
        ["git", "diff", "--quiet", "HEAD", "--"], cwd=checkout,
    ).returncode:
        raise ValueError(f"use the clean ACL2 checkout at {COMMIT}, tree {TREE}")
    acl2 = checkout / "saved_acl2"
    if not acl2.is_file():
        raise ValueError("build saved_acl2 with SBCL first")
    toy = HERE / "toy-defstobj.lsp"
    env = {**os.environ, "ACL2_CUSTOMIZATION": "NONE", "ACL2_SYSTEM_BOOKS": str(checkout / "books"),
           "X86ISA_EXEC": "nil", "LC_ALL": "C"}
    log = output.with_suffix(output.suffix + ".log")
    with tempfile.TemporaryDirectory(prefix="acl2-toy-defstobj-") as directory:
        staging = Path(directory) / "world.json"
        commands = (
            "(set-ld-error-action '(:exit 1) state)\n"
            + toy.read_text(encoding="utf-8")
            + ":q\n(handler-case (progn\n"
            f'  (load {lisp_string(TOOLS / "x86-run.lisp")})\n'
            f'  (load {lisp_string(HERE / "toy-defstobj-world.lsp")})\n'
            f'  (export-toy-defstobj {lisp_string(staging)}) (sb-ext:exit :code 0))\n'
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
        "toy_source_sha256": digest(toy),
    }
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
