#!/usr/bin/env python3
"""Export X86-RUN and X86-RUN-HALTED from the pinned certified ACL2 world."""

import argparse
import os
from pathlib import Path
import subprocess
import tempfile

from inventory import COMMIT, NATIVE_INPUTS, PROJECT, digest, lisp_string


TREE = "66d80ea68f664b931f8982b607fe2305f3cec0e4"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="pinned SBCL ACL2 checkout and certificates")
    parser.add_argument("output", type=Path, help="JSON destination")
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    commit, tree = subprocess.check_output(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"], cwd=checkout, text=True,
    ).splitlines()
    if (commit, tree) != (COMMIT, TREE):
        parser.error(f"use ACL2 8.7 at commit {COMMIT}, tree {TREE}")
    if subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=checkout).returncode:
        parser.error("the ACL2 checkout has tracked changes")

    books = checkout / "books"
    project = books / PROJECT
    if any((project / name).exists() for name in NATIVE_INPUTS):
        parser.error("use the X86ISA_EXEC=nil checkout without generated syscall inputs")
    acl2 = checkout / "saved_acl2"
    source = project / "machine/x86.lisp"
    if not acl2.is_file() or not source.with_suffix(".cert").is_file():
        parser.error("build saved_acl2 with SBCL and certify machine/x86 first")

    tools = Path(__file__).resolve().parent
    env = {**os.environ, "ACL2_CUSTOMIZATION": "NONE", "ACL2_SYSTEM_BOOKS": str(books),
           "CERT_PL_NO_COLOR": "1", "LC_ALL": "C", "X86ISA_EXEC": "nil"}
    log = args.output.with_suffix(args.output.suffix + ".log")
    with tempfile.TemporaryDirectory(prefix="acl2-x86-run-") as directory:
        export = Path(directory) / "x86-run.json"
        operands = " ".join(map(lisp_string, (source, export, digest(source), commit, tree)))
        commands = (
            "(set-ld-error-action '(:exit 1) state)\n"
            '(include-book "machine/x86" :ttags nil :uncertified-okp nil '
            ':defaxioms-okp nil :skip-proofs-okp nil)\n'
            ":q\n(handler-case (progn\n"
            f'  (load {lisp_string(tools / "certificate.lisp")})\n'
            f'  (load {lisp_string(tools / "x86-run.lisp")})\n'
            f'  (c3-export-x86-run {operands}) (sb-ext:exit :code 0))\n'
            '  (error (condition) (format *error-output* "~a~%" condition) (sb-ext:exit :code 1)))\n'
        )
        with log.open("w") as output:
            result = subprocess.run([acl2], input=commands, text=True, cwd=project, env=env,
                                    stdout=output, stderr=subprocess.STDOUT)
        if result.returncode or not export.is_file():
            raise SystemExit(f"ACL2 export did not complete. See {log}")
        args.output.write_bytes(export.read_bytes())
    print(f"{digest(args.output)}  {args.output}")


if __name__ == "__main__":
    main()
