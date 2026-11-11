#!/usr/bin/env python3
"""Print the Lake targets `make check` builds, one line, space-separated.

Without --base: every library and executable in lakefile.toml. With --base: only
what the diff from that revision can change. That is each changed module and every
module importing it, the modules whose `include_str`/`include_bytes` files or
library `needs` inputs changed, and all executables when the release suites must
run again. A change to the build configuration or to CI selects everything; a
change Lake never reads selects nothing.
"""

import argparse
import json
import os
import re
import subprocess
import tomllib
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]
# Any change here can change every build: run the full check.
FULL = ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "Makefile",
        "scripts/ci-scope.py", ".github/")
RELEASE = "tools/binaryen-lean/"
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»]+)", re.M)
INCLUDE = re.compile(r'include_(?:str|bytes)\s+"([^"]+)"')


def imports(text):
    return [dep.replace("«", "").replace("»", "") for dep in IMPORT.findall(text)]


def modules(config):
    """Map each module Lake can build here to its file and the library or executable owning it."""
    found = {}
    for lib in config.get("lean_lib", []):
        src = ROOT / lib.get("srcDir", ".")
        for glob in lib.get("globs", [lib["name"]]):
            prefix = glob.removesuffix(".*")
            top = src / prefix.replace(".", "/")
            files = [top.with_suffix(".lean")] + (sorted(top.rglob("*.lean")) if glob.endswith(".*") else [])
            for path in files:
                if path.is_file():
                    found[".".join(path.relative_to(src).with_suffix("").parts)] = (path, lib["name"])
    for exe in config.get("lean_exe", []):
        found[exe["root"]] = (ROOT / exe.get("srcDir", ".") / (exe["root"] + ".lean"), exe["name"])
    return found


def affected(config, found, changed):
    """The modules the changed files can change, with every module importing them."""
    seeds = set()
    for path in changed:
        stem = PurePosixPath(path).with_suffix("")
        for lib in [*config.get("lean_lib", []), *config.get("lean_exe", [])]:
            src = PurePosixPath(lib.get("srcDir", "."))
            if path.endswith(".lean") and stem.is_relative_to(src):
                seeds.add(".".join(stem.relative_to(src).parts))
    # Lake mixes a library's `needs` inputs into the trace of each of its modules.
    inputs = {i["name"]: i["path"] for i in [*config.get("input_dir", []), *config.get("input_file", [])]}
    needy = {lib["name"] for lib in config.get("lean_lib", [])
             if any(p == inputs[n] or p.startswith(inputs[n] + "/")
                    for n in lib.get("needs", []) for p in changed)}
    importers = {}
    for name, (path, owner) in found.items():
        text = path.read_text()
        for dep in imports(text):
            importers.setdefault(dep, set()).add(name)
        # Lake does not trace files read while elaborating; map them here.
        for include in INCLUDE.findall(text):
            if os.path.relpath(path.parent / include, ROOT).replace(os.sep, "/") in changed:
                seeds.add(name)
        if owner in needy:
            seeds.add(name)
    closure, todo = set(), list(seeds)
    while todo:
        name = todo.pop()
        if name not in closure:
            closure.add(name)
            todo.extend(importers.get(name, ()))
    # A deleted module seeds its importers but is no target itself.
    return {name for name in closure if name in found}


def select(changed):
    """The Lake targets for these changed paths; None means every target."""
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    exes = [exe["name"] for exe in config.get("lean_exe", [])]
    if changed is None or any(path.startswith(FULL) for path in changed):
        return [lib["name"] for lib in config.get("lean_lib", [])] + exes
    found = modules(config)
    hit = affected(config, found, changed)
    manifest = json.loads((ROOT / RELEASE / "release-manifest.json").read_text())
    proof_roots = {proof["module"] for tool in
                   [*manifest["tools"], *manifest["cli_compatibility"]["executables"]]
                   for proof in tool.get("proof_roots", [])}
    roots = {exe["root"] for exe in config.get("lean_exe", [])}
    release = any(p.startswith(RELEASE) for p in changed) or bool(hit & (roots | proof_roots))
    # Lake builds a target's imports first, so a module another target imports is implied.
    implied = {dep for name in hit for dep in imports(found[name][0].read_text())}
    # `+Module` names the module; a bare `Silmaril` would be the whole library.
    return sorted("+" + name for name in hit - implied - roots) + (exes if release else [])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", help="revision the diff starts from")
    args = parser.parse_args()
    changed = None if args.base is None else set(subprocess.run(
        ["git", "diff", "--name-only", "--no-renames", args.base, "HEAD"], cwd=ROOT,
        capture_output=True, text=True, check=True).stdout.split())
    print(" ".join(select(changed)))


if __name__ == "__main__":
    main()
