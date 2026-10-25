#!/usr/bin/env python3
"""Check release inventory references and isolated runtime import boundaries."""

import json
import re
import tomllib
from functools import cache
from pathlib import Path


root = Path(__file__).resolve().parents[2]
manifest = json.loads((Path(__file__).with_name("release-manifest.json")).read_text())
executables = {item["name"]: item for item in tomllib.loads(
    (root / "lakefile.toml").read_text())["lean_exe"]}


def module_path(module):
    path = root.joinpath(*module.split(".")).with_suffix(".lean")
    assert path.is_file(), f"Missing module {module}"
    return path


def code(text):
    """Erase nested Lean comments before reading import declarations."""
    result, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                result.append("\n")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


closures = {}


def closure(module):
    if module in closures:
        return closures[module]
    modules = {module}
    imports = re.findall(r"^(?:(?:public|private) )?import\s+(?:all\s+)?(Silmaril\.[\w.]+)",
                         code(module_path(module).read_text()), re.M)
    for imported in imports:
        modules.update(closure(imported))
    closures[module] = modules
    return modules


def check_entry(binary, entrypoint, runtime):
    item = executables[binary]
    assert entrypoint == str(Path(item["srcDir"]) / (item["root"] + ".lean"))
    entry = root / entrypoint
    imports = re.findall(r"^import\s+([\w.]+)", code(entry.read_text()), re.M)
    assert any(runtime in closure(imported) for imported in imports), entrypoint


@cache
def declarations(module):
    """Read qualified source declaration names; this is not a Lean proof check."""
    frames = []
    names = {}
    for line in code(module_path(module).read_text()).splitlines():
        line = line.strip()
        namespace = re.match(r"namespace\s+([\w.]+)\s*$", line)
        if namespace:
            frames.append(namespace[1])
            continue
        if re.match(r"(?:(?:public|private|noncomputable) )?section(?:\s+\w+)?\s*$", line):
            frames.append(None)
            continue
        if re.match(r"end(?:\s+[\w.]+)?\s*$", line):
            if frames:
                frames.pop()
            continue
        declaration = re.match(
            r"(?:@\[[^]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
            r"(theorem|def|abbrev|opaque)\s+([\w.?'!]+)(?=\s|\{|\(|:|$)", line)
        if declaration:
            kind, name = declaration.groups()
            if name.startswith("_root_."):
                names[name.removeprefix("_root_.")] = kind
            else:
                prefix = ".".join(frame for frame in frames if frame is not None)
                names[prefix + "." + name if prefix else name] = kind
    return names


def check_proofs(proofs):
    for proof in proofs:
        names = declarations(proof["module"])
        for theorem in proof["theorems"]:
            assert names.get(theorem) == "theorem", f"Missing qualified theorem {theorem} in {proof['module']}"


def check_pure_entrypoints(tool, inherited):
    """Bind the seven selected CLI paths to their separately checked pure APIs."""
    runtime_modules = closure(tool["runtime_root"])
    proof_modules = set()
    for proof in [*inherited["proof_roots"], *tool.get("proof_roots", [])]:
        proof_modules.update(closure(proof["module"]))
    for endpoint in tool["pure_entrypoints"]:
        assert any(declarations(module).get(endpoint) in {"def", "abbrev", "opaque"}
                   for module in runtime_modules), (
            tool["binary"], "pure endpoint missing from runtime", endpoint)
        assert any(declarations(module).get(endpoint) in {"def", "abbrev", "opaque"}
                   for module in proof_modules), (
            tool["binary"], "pure endpoint missing from proof closure", endpoint)


frontend = manifest["frontend"]
check_entry(frontend["binary"], frontend["entrypoint"], frontend["runtime_root"])
for fragment in manifest["forbidden_runtime_fragments"]:
    assert not any(fragment in module for module in closure(frontend["runtime_root"])), fragment
tools = manifest["tools"] + manifest["additional_standalones"]
for tool in tools:
    runtime = tool["runtime_root"]
    runtime_modules = closure(runtime)
    for fragment in manifest["forbidden_runtime_fragments"]:
        assert not any(fragment in module for module in runtime_modules), (runtime, fragment)
    binary = tool.get("standalone") or tool.get("binary")
    if binary:
        check_entry(binary, tool["entrypoint"], runtime)
    check_proofs(tool["proof_roots"])

for tool in manifest.get("cli_compatibility", {}).get("executables", []):
    assert tool["contract_from_command"] in {item["command"] for item in manifest["tools"]}
    check_entry(tool["binary"], tool["entrypoint"], tool["runtime_root"])
    for fragment in manifest["forbidden_runtime_fragments"]:
        assert not any(fragment in module for module in closure(tool["runtime_root"])), tool["binary"]
    check_proofs(tool.get("proof_roots", []))
    inherited = next(item for item in manifest["tools"]
                     if item["command"] == tool["contract_from_command"])
    check_pure_entrypoints(tool, inherited)

for runtime, excluded in manifest["standalone_isolation"].items():
    assert not set(excluded) & closure(runtime), runtime

assert all(tool["status"] == "not_implemented" for tool in manifest["missing_tools"])
print(f"Release manifest references pass; {len(manifest['tools'])} frontend commands, "
      f"{len(manifest['missing_tools'])} explicit missing tools")
print("Standalone import isolation and selected pure-endpoint references pass")
print("Inventory/source checks only: run the Lean proof-root build separately")
