#!/usr/bin/env python3
"""Export a bounded call graph from the certified ACL2 8.7 x86isa world."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
from check_dependencies import (BOOK, HEADER, STEP, WORLD_CLASSES, check, direct_calls,
                                encode_symbol, read_run, require)
from check_x86_run import EXPORT_SHA256, NIL, RUN, formals, symbol
from export_x86_run import TREE
from inventory import COMMIT, NATIVE_INPUTS, digest, lisp_string


def assemble(native, source_hash):
    root_rows, body_rows, world_rows = native
    roots = [{"requested": requested, "resolved": resolved, "via": via}
             for requested, resolved, via in sorted(root_rows)]
    owners = {symbol(resolved): symbol(requested) for requested, resolved, _ in root_rows}
    by_owner = {}
    step_bytes = None
    run = read_run()
    for name, parameters, body, native_calls in body_rows:
        owner = symbol(name)
        calls = direct_calls(body, formals(parameters))
        native_names = [] if native_calls == NIL else native_calls
        require(set(calls) == set(map(symbol, native_names)),
                f"call heads disagree with ACL2 all-fnnames for {owner}")
        by_owner[owner] = [[encode_symbol(callee), arity] for callee, arity in sorted(calls.items())]
        if owners[owner] == RUN:
            require((name, parameters, body) == (run["name"], run["formals"], run["body"]),
                    "live X86-RUN disagrees with the existing pinned export")
        elif owners[owner] == STEP:
            # The body is a translated term fixture, so keep its serialization compact.
            step_bytes = (json.dumps({"name": name, "formals": parameters, "body": body},
                                     separators=(",", ":")) + "\n").encode("utf-8")
    require(step_bytes is not None, "missing logical step body")
    declarations = []
    for name, arity, world in sorted(world_rows):
        fn = symbol(name)
        declarations.append({"id": name, "arity": None if arity == NIL else arity, "world": world,
                             "kind": "checked" if fn == RUN else WORLD_CLASSES[world],
                             "calls": by_owner.get(fn)})
    manifest = {**HEADER, "book_sha256": source_hash, "run_export_sha256": EXPORT_SHA256,
                "step_body_sha256": sha256(step_bytes).hexdigest(), "roots": roots,
                "declarations": declarations,
                "frontier": [row["id"] for row in declarations
                             if row["calls"] is None and row["kind"] != "primitive"]}
    check(manifest, step_bytes)
    return manifest, step_bytes


def read_world(checkout, log, driver="c3-export-dependencies", library=None, operands=()):
    """Read logical world properties after the same pinned certified root include."""
    checkout = checkout.resolve()
    commit, tree = subprocess.check_output(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"], cwd=checkout, text=True,
    ).splitlines()
    if (commit, tree) != (COMMIT, TREE):
        raise ValueError(f"use ACL2 8.7 at commit {COMMIT}, tree {TREE}")
    if subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=checkout).returncode:
        raise ValueError("the ACL2 checkout has tracked changes")
    books = checkout / "books"
    source = books / BOOK
    project = source.parent.parent
    if any((project / name).exists() for name in NATIVE_INPUTS):
        raise ValueError("use the X86ISA_EXEC=nil checkout without generated syscall inputs")
    acl2 = checkout / "saved_acl2"
    if not acl2.is_file() or not source.with_suffix(".cert").is_file():
        raise ValueError("build saved_acl2 with SBCL and certify machine/x86 first")

    env = {**os.environ, "ACL2_CUSTOMIZATION": "NONE", "ACL2_SYSTEM_BOOKS": str(books),
           "CERT_PL_NO_COLOR": "1", "LC_ALL": "C", "X86ISA_EXEC": "nil"}
    with tempfile.TemporaryDirectory(prefix="acl2-x86-dependencies-") as directory:
        exported = Path(directory) / "world.json"
        support = f'  (load {lisp_string(TOOLS / library)})\n' if library else ""
        arguments = " ".join([lisp_string(source), lisp_string(exported), *operands])
        commands = (
            "(set-ld-error-action '(:exit 1) state)\n"
            '(include-book "machine/x86" :ttags nil :uncertified-okp nil '
            ':defaxioms-okp nil :skip-proofs-okp nil)\n'
            ":q\n(handler-case (progn\n"
            f'  (load {lisp_string(TOOLS / "certificate.lisp")})\n'
            f'  (load {lisp_string(TOOLS / "x86-run.lisp")})\n'
            f'  (load {lisp_string(TOOLS / "dependencies.lisp")})\n'
            f"{support}  ({driver} {arguments})\n"
            '  (sb-ext:exit :code 0))\n'
            '  (error (condition) (format *error-output* "~a~%" condition) (sb-ext:exit :code 1)))\n'
        )
        with log.open("w") as output:
            result = subprocess.run([acl2], input=commands, text=True, cwd=project, env=env,
                                    stdout=output, stderr=subprocess.STDOUT)
        if result.returncode or not exported.is_file():
            raise ValueError(f"ACL2 export did not complete. See {log}")
        return json.loads(exported.read_bytes()), digest(source)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="pinned ACL2 SBCL checkout and certificates")
    parser.add_argument("output", type=Path, help="directory for the manifest and step evidence")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    try:
        manifest, step = assemble(*read_world(args.checkout, args.output / "export.log"))
    except ValueError as error:
        parser.exit(1, f"{error}\n")
    outputs = {"manifest.json": (json.dumps(manifest, indent=2) + "\n").encode("utf-8"),
               "step-body.json": step}
    for name, data in outputs.items():
        path = args.output / name
        path.write_bytes(data)
        print(f"{digest(path)}  {path}")


if __name__ == "__main__":
    main()
