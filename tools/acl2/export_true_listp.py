#!/usr/bin/env python3
"""Export stock ACL2 8.7 TRUE-LISTP and check the committed fixture."""

import argparse
from hashlib import sha256
import os
from pathlib import Path
import subprocess
import tempfile

COMMIT = "bc6f4f49e81a0711214a8d91f0d06e0e084d2204"
TREE = "66d80ea68f664b931f8982b607fe2305f3cec0e4"
AXIOMS_SHA = "50247ed0609257bcf08c4c6d365ccf1695bd2cbd2dfedff0f7bc516f9ce828b1"
TOOLS = Path(__file__).resolve().parent
FIXTURE = TOOLS.parents[1] / "corpus/acl2/true-listp/acl2-8.7.sexp"


def lisp_string(value):
    return '"' + str(value).replace("\\", "\\\\").replace('"', '\\"') + '"'


def export(checkout):
    revisions = subprocess.check_output(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"], cwd=checkout, text=True,
    ).splitlines()
    if revisions != [COMMIT, TREE]:
        raise SystemExit(f"Use the pinned ACL2 8.7 commit {COMMIT}")
    if subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=checkout).returncode:
        raise SystemExit("The ACL2 checkout has tracked changes")
    if sha256((checkout / "axioms.lisp").read_bytes()).hexdigest() != AXIOMS_SHA:
        raise SystemExit("axioms.lisp differs from the pinned source")
    acl2 = checkout / "saved_acl2"
    if not acl2.is_file():
        raise SystemExit("Build saved_acl2 first with make LISP=sbcl")
    with tempfile.TemporaryDirectory(prefix="acl2-true-listp-") as directory:
        path = Path(directory) / "true-listp.sexp"
        arguments = " ".join(map(lisp_string, [path, COMMIT, TREE, AXIOMS_SHA]))
        commands = (
            ":q\n(handler-case (progn\n"
            f"  (load {lisp_string(TOOLS / 'true-listp.lisp')})\n"
            f"  (silmaril-export-true-listp {arguments})\n"
            "  (sb-ext:exit :code 0))\n"
            "  (error (c) (format *error-output* \"~a~%\" c) (sb-ext:exit :code 1)))\n"
        )
        result = subprocess.run(
            [acl2], input=commands, text=True, cwd=checkout,
            env={**os.environ, "ACL2_CUSTOMIZATION": "NONE", "LC_ALL": "C"},
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        if result.returncode or not path.is_file():
            raise SystemExit(result.stdout)
        return path.read_bytes()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--output", type=Path, help="write the export here instead of checking the fixture")
    args = parser.parse_args()
    data = export(args.checkout.resolve())
    if args.output:
        args.output.write_bytes(data)
    elif data != FIXTURE.read_bytes():
        raise SystemExit("Stock ACL2 export differs from the committed TRUE-LISTP fixture")
    print(f"TRUE-LISTP export SHA-256 {sha256(data).hexdigest()}")


if __name__ == "__main__":
    main()
