#!/usr/bin/env python3
"""Fixtures of the compiler explorer: builds, listings and problem manifests.

    python3 -I tools/compiler-explorer/fixtures.py build      # Docker: compile the demo programs
    python3 -I tools/compiler-explorer/fixtures.py listings   # Docker: objdump the compiles-to objects
    python3 -I tools/compiler-explorer/fixtures.py decompile  # Docker and Lean: the decompiled fixture
    python3 -I tools/compiler-explorer/fixtures.py manifests [--out DIR]  # no Docker: the manifests
    python3 -I tools/compiler-explorer/fixtures.py stages [--check]  # exact standalone Ail and Core
    python3 -I tools/compiler-explorer/fixtures.py viewer --out SITE    # exact C/ELF viewer assets
    python3 -I tools/compiler-explorer/fixtures.py include-map MANIFEST OUT  # pinned image header bytes

`build` and `listings` run the pinned gcc image of tools/c-tv (by digest), with no network by
default (`CEXPLORER_DOCKER_NETWORK` overrides it), the caller's uid and sources mounted read-only.
They write what they produced and a receipt (image digest, command, tool versions and hashes, input and output
SHA-256) under examples/compiler-explorer/. `manifests` reads only committed files and is
deterministic: the manifests are a function of the sources, the receipts, the listings and
the c-tv correspondences.

Nothing here decides a proof status. A manifest names, per obligation, the Lean statement and
(when one exists) the theorem claimed to prove it; tools/compiler-explorer/export.lean decides
the status from the Lean build.
"""

from __future__ import annotations

import hashlib
import io
import json
import os
import pathlib
import re
import subprocess
import sys
import tarfile
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
EX = ROOT / "examples" / "compiler-explorer"
PROGRAMS = EX / "programs"
BUILDS = EX / "builds"
MANIFESTS = EX / "manifests"
COMPILES_TO = ROOT / "examples" / "compiles-to"
LISTINGS = EX / "compiles-to"

IMAGE = ("gcc:13.3.0@sha256:"
         "1d71f0f3450214bef38fe09e6f610fb6cca90cf97b43f4ce845bfc32a4168818")
DOCKER_NETWORK = os.environ.get("CEXPLORER_DOCKER_NETWORK", "none")
OPTS = ["O0", "O2"]
S_FLAGS = ["-g", "-S", "-std=c11", "-fno-asynchronous-unwind-tables",
           "-fdebug-prefix-map=/src=."]
# The demo programs, in the order of the staged examples, with their link libraries.
PROGRAM_LIBS = {"hello": [], "msort": [], "fft": ["-lm"], "lisp": []}
# What each program should print, written down from its meaning (the FFT of four ones and four
# zeros: X_k = sum_{n<4} e^{-2 pi i k n / 8}), not copied from a run.
EXPECTED_STDOUT = {
    "hello": "hello, world\n",
    "msort": "1 2 3 4 5 6 7 8\n",
    "fft": ("0: +4.000 +0.000i\n1: +1.000 -2.414i\n2: +0.000 +0.000i\n3: +1.000 -0.414i\n"
            "4: +0.000 +0.000i\n5: +1.000 +0.414i\n6: +0.000 +0.000i\n7: +1.000 +2.414i\n"),
    "lisp": "11\n(1 2 3)\n",
}
SCHEMA = "silmaril.compiler-explorer.problem/1"
LEAN_MODULE = "CompilesToExamples.Explorer.Builds"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_ref(path: pathlib.Path, media: str) -> dict:
    data = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "sha256": sha256(data),
            "size": len(data), "media": media}


def dump(path: pathlib.Path, obj) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True, ensure_ascii=False) + "\n")


def docker(mounts: list[tuple[pathlib.Path, str, bool]], script: str) -> None:
    cmd = ["docker", "run", "--rm", "--network", DOCKER_NETWORK,
           "-u", f"{os.getuid()}:{os.getgid()}"]
    for host, guest, ro in mounts:
        cmd += ["-v", f"{host}:{guest}" + (":ro" if ro else "")]
    cmd += ["-w", "/src", IMAGE, "sh", "-eu", "-c", script]
    subprocess.run(cmd, check=True)


TOOLS = ('gcc --version | head -n1 > /out/gcc.txt; as --version | head -n1 > /out/as.txt; '
         'sha256sum "$(gcc -print-prog-name=cc1)" "$(command -v as)" "$(command -v ld)" '
         '> /out/tools.txt')


def build() -> None:
    """Compile each program at each level to assembly, assemble and link that assembly, and run it."""
    for prog, libs in PROGRAM_LIBS.items():
        src = PROGRAMS / f"{prog}.c"
        for opt in OPTS:
            out = BUILDS / prog / opt
            out.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory() as tmp:
                compile_cmd = " ".join(["gcc", f"-{opt}", *S_FLAGS, f"{prog}.c", "-o", f"/out/{prog}.s"])
                link_cmd = " ".join(["gcc", f"/out/{prog}.s", "-o", f"/out/{prog}", *libs])
                docker([(PROGRAMS, "/src", True), (pathlib.Path(tmp), "/out", False)],
                       f"{compile_cmd}; {link_cmd}; set +e; /out/{prog} > /out/stdout.txt; "
                       f"echo $? > /out/exit.txt; set -e; {TOOLS}")
                t = pathlib.Path(tmp)
                asm = (t / f"{prog}.s").read_bytes()
                (out / f"{prog}.s").write_bytes(asm)
                stdout = (t / "stdout.txt").read_bytes()
                receipt = {
                    "image": IMAGE, "workdir": "/src", "network": DOCKER_NETWORK,
                    "command": compile_cmd.replace("/out/", ""),
                    "gcc": (t / "gcc.txt").read_text().strip(),
                    "as": (t / "as.txt").read_text().strip(),
                    "tools_sha256": (t / "tools.txt").read_text().strip().splitlines(),
                    "source": {"path": f"{prog}.c", "sha256": sha256(src.read_bytes())},
                    "assembly": {"path": f"{opt}/{prog}.s", "sha256": sha256(asm), "size": len(asm)},
                }
                run = {
                    "kind": "execution",
                    "what": ("the assembly above, assembled and linked by the same image against its "
                             "glibc, run once in the container with no input"),
                    "link": link_cmd.replace("/out/", ""),
                    "run": f"./{prog}",
                    "assembly_sha256": sha256(asm),
                    "exit": int((t / "exit.txt").read_text().strip()),
                    "stdout": stdout.decode("utf-8"),
                    "stdout_sha256": sha256(stdout),
                }
                dump(out / "RECEIPT.json", receipt)
                dump(out / "run.json", run)
                print(f"built {prog} -{opt}: {len(asm)} bytes of assembly, exit {run['exit']}")


def listings() -> None:
    """objdump the committed compiles-to objects (the bytes the Lean statements are about)."""
    for name in sorted(p.name for p in COMPILES_TO.iterdir() if (p / f"{p.name}.c").exists()):
        for opt in OPTS:
            obj_dir = COMPILES_TO / name / opt
            obj = obj_dir / f"{name}.o"
            if not obj.exists():
                continue
            out = LISTINGS / name / opt
            out.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory() as tmp:
                cmd = f"objdump -d -w -j .text {name}.o"
                docker([(obj_dir, "/src", True), (pathlib.Path(tmp), "/out", False)],
                       f"{cmd} > /out/listing.txt; objdump --version | head -n1 > /out/objdump.txt")
                t = pathlib.Path(tmp)
                text = (t / "listing.txt").read_bytes()
                (out / "listing.txt").write_bytes(text)
                dump(out / "RECEIPT.json", {
                    "image": IMAGE, "workdir": "/src", "network": DOCKER_NETWORK, "command": cmd,
                    "objdump": (t / "objdump.txt").read_text().strip(),
                    "object": {"path": f"examples/compiles-to/{name}/{opt}/{name}.o",
                               "sha256": sha256(obj.read_bytes())},
                    "listing": {"path": "listing.txt", "sha256": sha256(text), "size": len(text)},
                })
                print(f"listed {name} -{opt}")


# ---------------------------------------------------------------------------------------------
# The preprocessor's environment: predefined macros, search order and included files, as the
# pinned compiler reports them (`gcc -dM -E`, `gcc -E -v`, `gcc -M`, `gcc -E -dI -H`).

ENV = EX / "env"
CT_FLAGS = ("-g -c -fdebug-prefix-map=/src=. -std=c11 -ffreestanding -fno-builtin -fno-stack-protector "
            "-fcf-protection=none -mgeneral-regs-only -fno-pic -fno-pie -fno-asynchronous-unwind-tables "
            "-fno-unwind-tables -fno-ident")


PP_MARKER = re.compile(r'# (\d+) "([^"\\]*)"((?: [1-4])*)')
PP_INCLUDE = re.compile(r'#(include|include_next|import) (<[^>\n]+>|"[^"\n]+")')
LITERAL_INCLUDE = re.compile(r'^\s*#\s*(include|include_next|import)\s*(<[^>\n]+>|"[^"\n]+")'
                             r'\s*(?://.*|/\*[^\n]*\*/\s*)?$')
HEADER_ENTRY = re.compile(r'(\.+) (.+)')


def include_path(name: str) -> str:
    return name if name.startswith(('/', '<')) else '/src/' + name


def include_occurrences(pp: str, headers: str, source: str, contents: dict[str, bytes]) -> list[dict]:
    """Pair GCC's -dI events with enter/return markers, checking physical entries against -H."""
    out = []
    stack = []
    opened = []
    path, number, pending = include_path(source), 0, None
    lines = {name: data.decode('utf-8', errors='replace').split('\n') for name, data in contents.items()}
    for line in pp.split('\n'):
        if match := PP_INCLUDE.fullmatch(line):
            directive, operand = match.groups()
            parent = stack[-1] if stack else None
            if path != (out[parent]['resolved'] if parent is not None else include_path(source)):
                raise ValueError(f"unexpected include location {path}:{number}")
            physical = lines[path][number - 1] if 0 < number <= len(lines[path]) else ''
            literal = LITERAL_INCLUDE.fullmatch(physical)
            pending = len(out)
            out.append({"directive": directive, "operand": operand, "from": path, "line": number,
                        "literal": literal is not None and literal.groups() == (directive, operand),
                        "parent": parent, "resolved": None})
            number += 1
        elif match := PP_MARKER.fullmatch(line):
            lineno, file, flags = match.groups()
            dest = include_path(file)
            flags = flags.split()
            if '1' in flags:
                if dest not in contents:
                    raise ValueError(f"GCC entered a file missing from the input set: {dest}")
                if pending is not None:
                    out[pending]['resolved'] = dest
                    opened.append((len(stack) + 1, dest))
                elif path == '<command-line>' and not stack:
                    pending = len(out)
                    out.append({"directive": "implicit", "parent": None, "resolved": dest})
                else:
                    raise ValueError(f"unpaired GCC file entry {dest}")
                stack.append(pending)
                pending = None
            elif '2' in flags:
                if not stack or out[stack.pop()].get('from', '<command-line>') != dest:
                    raise ValueError(f"unpaired GCC file return {dest}")
                pending = None
            elif pending is not None and (dest != path or int(lineno) != out[pending]['line']):
                pending = None
            path, number = dest, int(lineno)
        else:
            number += 1
            pending = None
    expected = [(len(match[1]), include_path(match[2])) for line in headers.splitlines()
                if (match := HEADER_ENTRY.fullmatch(line))]
    if stack or opened != expected:
        raise ValueError("GCC include directives and header entries did not agree")
    return out


def capture_includes(prog: str, flags: str, directory: pathlib.Path) -> dict:
    source = f"{prog}.c"
    mounts = [(PROGRAMS, "/src", True), (directory, "/out", False)]
    docker(mounts, f"gcc {flags} -M -MT fixture {source} > /out/deps; "
                   f"gcc {flags} -E -dI -H {source} > /out/preprocessed 2> /out/headers")
    stem, deps = (directory / "deps").read_text().replace('\\\n', ' ').split(':', 1)
    names = deps.split()
    if stem != 'fixture' or not names or names[0] != source or any(
            not re.fullmatch(r'[a-zA-Z0-9._+/\-]+', name) for name in names):
        raise ValueError("unsupported GCC make dependency spelling; refusing to guess header paths")
    headers = sorted(set(names[1:]))
    (directory / 'header-paths').write_text(''.join(f'{name}\n' for name in headers))
    docker(mounts, "tar -chf /out/headers.tar --no-recursion --verbatim-files-from -T /out/header-paths")
    files, contents = [], {include_path(source): (PROGRAMS / source).read_bytes()}
    with tarfile.open(directory / 'headers.tar') as archive:
        for name in headers:
            data = archive.extractfile(name.lstrip('/')).read()
            path = include_path(name)
            files.append({"path": path, "sha256": sha256(data), "size": len(data)})
            contents[path] = data
    occurrences = include_occurrences((directory / 'preprocessed').read_text(),
                                      (directory / 'headers').read_text(), source, contents)
    if {event['resolved'] for event in occurrences if event['resolved']} != {entry['path'] for entry in files}:
        raise ValueError("GCC include entries and dependency files did not agree")
    return {"image": IMAGE, "flags": flags, "source": source, "files": files,
            "source_sha256": sha256(contents[include_path(source)]),
            "trace": {"method": "gcc -E -dI -H", "occurrences": occurrences}}


def preprocessor_env() -> None:
    ENV.mkdir(parents=True, exist_ok=True)
    jobs = [(f"compiles-to-{opt}", f"-{opt} {CT_FLAGS}", None) for opt in OPTS]
    jobs += [(f"programs-{opt}", f"-{opt} " + " ".join(S_FLAGS[:1] + S_FLAGS[2:]), None) for opt in OPTS]
    jobs += [(f"{prog}-{opt}", f"-{opt} " + " ".join(S_FLAGS[:1] + S_FLAGS[2:]), prog)
             for prog in PROGRAM_LIBS for opt in OPTS]
    for tag, flags, prog in jobs:
        with tempfile.TemporaryDirectory() as tmp:
            t = pathlib.Path(tmp)
            if prog is None:
                script = (f"gcc {flags} -dM -E -x c /dev/null | LC_ALL=C sort > /out/macros.h; "
                          f"gcc {flags} -E -v -x c /dev/null 2> /out/search.txt > /dev/null")
                docker([(PROGRAMS, "/src", True), (t, "/out", False)], script)
                (ENV / f"{tag}.macros.txt").write_bytes((t / "macros.h").read_bytes())
                lines = (t / "search.txt").read_text().splitlines()
                i = lines.index("#include <...> search starts here:")
                j = lines.index("End of search list.")
                dump(ENV / f"{tag}.search.json", {"image": IMAGE, "flags": flags,
                                                   "angle_search": [x.strip() for x in lines[i + 1:j]]})
            else:
                dump(ENV / f"{tag}.includes.json", capture_includes(prog, flags, t))
        print(f"env {tag}")


# ---------------------------------------------------------------------------------------------
# Fragments: content-addressed sets of ranges


def fragment(artifact_sha: str, space: str, ranges: list[list[int]], role: str, label: str) -> dict:
    """A fragment: ranges in one artifact's coordinate space, identified by their content address."""
    ranges = sorted([list(r) for r in ranges])
    fid = sha256(f"{artifact_sha}:{space}:{json.dumps(ranges)}".encode())[:20]
    return {"id": fid, "artifact": role, "space": space, "ranges": ranges, "label": label}


def line_ranges(data: bytes) -> list[tuple[int, int]]:
    """Byte range [start, end) of each line (1-based index = position + 1), without newline."""
    out, start = [], 0
    for i, b in enumerate(data):
        if b == 0x0A:
            out.append((start, i))
            start = i + 1
    if start < len(data):
        out.append((start, len(data)))
    return out


class Builder:
    def __init__(self, src_bytes: bytes, src_sha: str, tgt_sha: str, tgt_space: str):
        self.lines = line_ranges(src_bytes)
        self.src_sha, self.tgt_sha, self.tgt_space = src_sha, tgt_sha, tgt_space
        self.fragments: dict[str, dict] = {}
        self.edges: list[dict] = []

    def add(self, f: dict) -> str:
        self.fragments.setdefault(f["id"], f)
        return f["id"]

    def src_lines(self, lines: list[int]) -> str:
        ranges = [list(self.lines[n - 1]) for n in sorted(set(lines)) if 0 < n <= len(self.lines)]
        label = "line " + ",".join(str(n) for n in sorted(set(lines)))
        if len(set(lines)) > 1 and sorted(set(lines)) == list(range(min(lines), max(lines) + 1)):
            label = f"lines {min(lines)}-{max(lines)}"
        return self.add(fragment(self.src_sha, "bytes", ranges, "source", label))

    def tgt(self, ranges: list[list[int]], label: str) -> str:
        return self.add(fragment(self.tgt_sha, self.tgt_space, ranges, "target", label))


# ---------------------------------------------------------------------------------------------
# Assembly (gcc -S): the `.loc` directives, as a compiler explorer reads them

LOC = re.compile(r"^\s*\.loc\s+(\d+)\s+(\d+)")
FILE = re.compile(r'^\s*\.file\s+(\d+)\s+"([^"]*)"(?:\s+"([^"]*)")?')
LABEL = re.compile(r"^([A-Za-z_.$][\w.$]*):")


def is_instruction(line: str) -> bool:
    s = line.strip()
    return bool(s) and not s.startswith(".") and not s.startswith("#") and not LABEL.match(s)


def asm_navigation(b: Builder, asm: bytes, src_name: str) -> dict:
    """Navigation edges from `.loc`: per (function, source line), the instruction lines after a
    `.loc` of that line in that function. Debug information, not semantics."""
    files: dict[str, str] = {}
    cur_fn = None
    cur_loc: tuple[str, int] | None = None
    groups: dict[tuple[str, int], list[list[int]]] = {}
    other: dict[str, int] = {}
    unattributed = 0
    offset = 0
    for raw in asm.split(b"\n"):
        start, end = offset, offset + len(raw)
        offset = end + 1
        line = raw.decode("utf-8")
        if m := FILE.match(line):
            files[m.group(1)] = m.group(3) or m.group(2)
            continue
        if (m := LABEL.match(line)) and not m.group(1).startswith("."):
            cur_fn, cur_loc = m.group(1), None
            continue
        if m := LOC.match(line):
            cur_loc = (m.group(1), int(m.group(2)))
            continue
        if not is_instruction(line):
            continue
        if cur_loc is None or cur_fn is None:
            unattributed += 1
            continue
        fname = files.get(cur_loc[0], "?")
        if fname != src_name:
            other[fname] = other.get(fname, 0) + 1
            continue
        groups.setdefault((cur_fn, cur_loc[1]), []).append([start, end])
    for (fn, ln), ranges in sorted(groups.items(), key=lambda kv: (kv[0][0], kv[0][1])):
        s = b.src_lines([ln])
        t = b.tgt(ranges, f"{fn}: {len(ranges)} instruction(s) of line {ln}")
        b.edges.append({"id": f"nav/{fn}/{ln}", "kind": "navigation", "origin": "dwarf-loc",
                        "function": fn, "source": [s], "target": [t]})
    return {"unattributed_instructions": unattributed,
            "instructions_from_other_files": dict(sorted(other.items()))}


def program_manifests() -> list[dict]:
    out = []
    for prog in PROGRAM_LIBS:
        src = PROGRAMS / f"{prog}.c"
        for opt in OPTS:
            d = BUILDS / prog / opt
            receipt = json.loads((d / "RECEIPT.json").read_text())
            run = json.loads((d / "run.json").read_text())
            asm_path = d / f"{prog}.s"
            src_ref, asm_ref = file_ref(src, "text/x-c"), file_ref(asm_path, "text/x-asm")
            assert receipt["source"]["sha256"] == src_ref["sha256"], f"{prog}: source changed since build"
            assert receipt["assembly"]["sha256"] == asm_ref["sha256"], f"{prog}: assembly changed"
            b = Builder(src.read_bytes(), src_ref["sha256"], asm_ref["sha256"], "bytes")
            stats = asm_navigation(b, asm_path.read_bytes(), f"{prog}.c")
            obligations = [
                {"id": "translation", "kind": "translation", "decl": None, "statement": None,
                 "unsupported": ("no source semantics in Lean covers this program: the C "
                                 "elaborator of Silmaril.Project.CompilesTo has no loops, calls, "
                                 "pointers, floating point or I/O, and no x86 model here covers "
                                 "the linked program with glibc")},
                {"id": "abi", "kind": "abi", "decl": None, "statement": None,
                 "unsupported": "no ABI statement is attempted for this program"},
                {"id": "nonvacuity", "kind": "nonvacuity", "decl": None, "statement": None,
                 "unsupported": "no translation is stated, so there is nothing to be vacuous"},
                {"id": "mapping", "kind": "mapping", "decl": None, "statement": None,
                 "unsupported": "no semantic mapping: only the compiler's debug line table"},
                {"id": "refinement", "kind": "refinement", "decl": None, "statement": None,
                 "unsupported": "no comorphism relation is generated for this program"},
            ]
            out.append({
                "schema": SCHEMA,
                "id": f"programs/{prog}/{opt}",
                "title": f"{prog}.c, gcc 13.3.0 -{opt} (assembly)",
                "direction": "compiled",
                "artifacts": {"source": src_ref, "target": asm_ref,
                              "receipt": file_ref(d / "RECEIPT.json", "application/json"),
                              "run": file_ref(d / "run.json", "application/json"),
                              "include_search": file_ref(ENV / f"programs-{opt}.search.json", "application/json"),
                              "includes": file_ref(ENV / f"{prog}-{opt}.includes.json", "application/json"),
                              "macros": file_ref(ENV / f"programs-{opt}.macros.txt", "text/x-c")},
                "view": {"source": "source", "target": "target"},
                "problem_form": "relation",
                "relation": {"semantics": "none",
                             "description": "gcc 13.3.0 compiled this C to this assembly (receipt); the run test "
                                            "checks one execution; no Lean statement relates them"},
                "stages": [{"side": "target", "name": "gcc -S (cc1, pinned image)", "trust": "trusted",
                            "input": "source", "output": "target", "evidence": "receipt only"}],
                "include_env": include_env(src, ENV / f"programs-{opt}.search.json", receipt,
                                           ENV / f"{prog}-{opt}.includes.json"),
                "derivation": {"kind": "compiler", "compiler": "gcc", "version": receipt["gcc"],
                               "image": IMAGE, "command": receipt["command"], "opt": opt,
                               "target": "x86_64-linux-gnu", "receipt": "receipt"},
                "context": {
                    "source_model": None, "target_model": None, "abi": None,
                    "mapping_relation": None, "comorphism": None,
                },
                "fragments": sorted(b.fragments.values(), key=lambda f: f["id"]),
                "edges": b.edges,
                "navigation_stats": stats,
                "obligations": obligations,
                "tests": [{"id": "run", "kind": "execution", "artifact": "run",
                           "about": "target", "expected_stdout": EXPECTED_STDOUT[prog]}],
                "lean": {"family": None, "modules": []},
            })
    return out


# ---------------------------------------------------------------------------------------------
# The compiles-to examples: the objects the Lean statements are about

# The Lean theorems of CompilesToExamples.Explorer.Builds, per (file, build): its namespace, and
# whether every segment of the build is proved.
LEAN_BUILDS = {("straight", "O0"): ("StraightO0", True), ("straight", "O2"): ("StraightO2", True),
               ("branch", "O0"): ("BranchO0", True), ("branch", "O2"): ("BranchO2", False)}
OBJDUMP = re.compile(r"^\s*([0-9a-f]+):\t([0-9a-f ]+)\t(.*)$")


def cexplorer():
    """The database module, for its statement templates (one definition of each statement)."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("cexplorer", pathlib.Path(__file__).with_name("cexplorer.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def listing_rows(text: bytes) -> list[tuple[int, int, int, int]]:
    """(text offset, instruction length, byte start, byte end) of each instruction line."""
    rows, offset = [], 0
    for raw in text.split(b"\n"):
        start, end = offset, offset + len(raw)
        offset = end + 1
        if m := OBJDUMP.match(raw.decode("utf-8")):
            rows.append((int(m.group(1), 16), len(m.group(2).split()), start, end))
    return rows


def include_env(main: pathlib.Path, search: pathlib.Path, receipt: dict,
                includes: pathlib.Path | None = None) -> dict:
    """A content-addressed include environment observation, not a complete preprocessor trace."""
    workdir = receipt["workdir"]
    files = [{"name": f"{workdir}/{main.name}", "sha256": sha256(main.read_bytes()), "size": main.stat().st_size,
              "artifact": "source", "where": main.relative_to(ROOT).as_posix()}]
    dependencies = None
    if includes is not None:
        dependency_run = json.loads(includes.read_text())
        dependencies = {"artifact": "includes", "flags": dependency_run["flags"]}
        for header in dependency_run["files"]:
            files.append({"name": header["path"], "sha256": header["sha256"], "size": header["size"]})
    search_result = json.loads(search.read_text())
    return {"files": files, "workdir": workdir, "image": receipt["image"],
            "search": search_result["angle_search"], "search_receipt": "include_search",
            "macros": "macros", "probe_flags": search_result["flags"], "dependencies": dependencies,
            "options": receipt["command"].split(),
            "note": ("Main file and observed headers by content; macros/search come from a separate probe. "
                     "Header dependencies and include occurrences are GCC observations from a separate "
                     "preprocessing probe, not a verified preprocessor." if includes else
                     "Main file and observed headers by content; macros/search come from a separate probe. "
                     "Header dependencies, when present, are from the recorded gcc -M flags, not a replay "
                     "of every build. This is not a complete include map or a verified preprocessor.")}


def dwarf_facts(fn: dict, base: int, have_lean: bool) -> list[dict]:
    """What c-tv read from the object's DWARF (line table, frame slots), and what depends on it."""
    out = []
    for r in fn["ranges"]:
        out.append({"kind": "line_range", "origin": "DWARF line table (c-tv, gimli: unverified)",
                    "fact": f"line {r['line']} <- .text [{base + r['start']:#x}, {base + r['end']:#x})",
                    "used_by": ["navigation links"],
                    "if_wrong": "a wrong range misplaces a navigation link; no statement depends on it"})
    for p in fn["points"] if have_lean else []:
        out.append({"kind": "point", "origin": "DWARF line table (c-tv): point placement",
                    "fact": f"point {p['index']} at offset {p['off']:#x}, line {p['line']}",
                    "used_by": [f"edge/{p['index']}", f"point/{p['index']}", "mapping", "translation"],
                    "if_wrong": "the segment statements refer to these selected points, not to correctness of the extraction"})
        if isinstance(p["kind"], dict):
            for sl in p["kind"]["Slots"]:
                out.append({"kind": "frame_slot", "origin": "DWARF DW_AT_location (c-tv, gimli: unverified)",
                            "fact": f"point {p['index']}: {sl['name']} (line {sl['decl_line']}) at CFA{sl['off']:+d}, "
                                    f"{sl['size']} bytes{', defined' if sl['defined'] else ''}",
                            "used_by": [f"edge/{p['index']}", "refinement"],
                            "if_wrong": ("the chosen location relation changes; proving a theorem about it does not "
                                         "establish that this is the source variable's actual DWARF slot")})
    return out


PROBE = "Silmaril.Project.CompilesTo.Probe"
FRONTEND_FILES = {"ail": "typed-ail.sexp", "core": "core.sexp"}


def frontend_artifacts(directory: pathlib.Path, prefix: str = "") -> dict:
    return {prefix + role: file_ref(directory / name, "text/x-lisp") for role, name in FRONTEND_FILES.items()}


def frontend_alternatives(prefix: str = "") -> list[dict]:
    return [{"role": prefix + "ail", "label": "Typed Ail"}, {"role": prefix + "core", "label": "Core"}]


def frontend_files(check: bool = False) -> None:
    for directory in (COMPILES_TO / "straight", COMPILES_TO / "branch", C2C):
        probe = directory / "core-probe.txt"
        raw = probe.read_bytes().removesuffix(b"\n")
        begin = b"BEGIN-TYPED-AIL\n"
        boundary = b"\nEND-TYPED-AIL\nBEGIN-CORE-DOCUMENT\n"
        end = b"END-CORE-DOCUMENT"
        ail, separator, core = raw.removeprefix(begin).removesuffix(end).partition(boundary)
        if not raw.startswith(begin) or not raw.endswith(end) or not separator or not ail or not core.endswith(b"\n"):
            raise ValueError(f"{probe}: expected one typed Ail value followed by its Core document")
        for role, content in (("ail", ail), ("core", core)):
            target = directory / FRONTEND_FILES[role]
            if check:
                if target.read_bytes() != content:
                    raise ValueError(f"{target}: does not match its probe payload")
            else:
                target.write_bytes(content)


def compiles_to_manifests() -> list[dict]:
    cx = cexplorer()
    out = []
    for name in ["straight", "branch", "loop"]:
        src = COMPILES_TO / name / f"{name}.c"
        corr = json.loads((COMPILES_TO / name / "correspondence.json").read_text())
        cname = name.capitalize()
        for opt in OPTS:
            obj = COMPILES_TO / name / opt / f"{name}.o"
            receipt_path = COMPILES_TO / name / opt / "RECEIPT.json"
            receipt = json.loads(receipt_path.read_text())
            lst = LISTINGS / name / opt / "listing.txt"
            lst_receipt = json.loads((LISTINGS / name / opt / "RECEIPT.json").read_text())
            src_ref, obj_ref = file_ref(src, "text/x-c"), file_ref(obj, "application/x-elf-relocatable")
            lst_ref = file_ref(lst, "text/x-objdump")
            assert receipt["object"]["sha256"] == obj_ref["sha256"]
            assert lst_receipt["object"]["sha256"] == obj_ref["sha256"], "listing of another object"
            assert lst_receipt["listing"]["sha256"] == lst_ref["sha256"]
            rows = listing_rows(lst.read_bytes())
            for fn in corr[opt]:
                fname = fn["name"]
                b = Builder(src.read_bytes(), src_ref["sha256"], obj_ref["sha256"], "text-offset")
                base = fn["off"]
                notes = {(u["line"], u["start"]): u["reason"] for u in fn.get("unsupported", [])}
                # navigation: the DWARF line table, as c-tv read it (`ranges`)
                for r in fn["ranges"]:
                    s = b.src_lines([r["line"]])
                    t = b.tgt([[base + r["start"], base + r["end"]]],
                              f"[{base + r['start']:#x}, {base + r['end']:#x})")
                    e = {"id": f"nav/{fname}/{r['line']}/{r['start']}", "kind": "navigation",
                         "origin": "dwarf-line-table", "function": fname, "source": [s], "target": [t]}
                    if (r["line"], r["start"]) in notes:
                        e["note"] = "no statement-level point (c-tv): " + notes[(r["line"], r["start"])]
                    b.edges.append(e)
                ns, proved = LEAN_BUILDS.get((name, opt), (None, False))
                unsupported_reason = fn.get("function_unsupported")
                pts = [] if unsupported_reason or ns is None else fn["points"]
                F = f"CompilesToExamples.{cname}.{opt}.{fname}"
                lean_vars = {"fn": F, "ail": f"CompilesToExamples.{cname}.ail", "cname": fname,
                             "isa": "Silmaril.X86.Open.isa",
                             "comorphism": "Silmaril.Project.CompilesTo.dwarf",
                             "target_value": f"silmaril.compiles_to.{name}.{opt.lower()}.obj",
                             "listing": f"CompilesToExamples.{cname}.{opt}.{fname}Listing"}
                X = f"CompilesToExamples.Explorer.{ns}"

                row_kind = {"translation": "translation", "nonvacuity": "nonvacuous", "mapping": "mapping",
                            "refinement": "location", "artifact": "code"}

                def ob(oid, kind, decl, edge=None, point=None, line=None):
                    o = {"id": oid, "kind": kind, "decl": decl,
                         "statement": cx.statement_for("c-function-x86", lean_vars, kind, point, line)}
                    if edge:
                        o["edge"] = edge
                    rk = f"edge_{point}" if kind == "edge" else row_kind.get(kind)
                    if rk:
                        o["row"] = row_name(name, opt, fname, rk)
                    return o

                obligations = []
                last_line = max(r["line"] for r in fn["ranges"])
                for i, p in enumerate(pts):
                    lo = p["line"]
                    hi = pts[i + 1]["line"] if i + 1 < len(pts) else last_line + 1
                    end = pts[i + 1]["off"] if i + 1 < len(pts) else fn["size"]
                    s = b.src_lines(list(range(lo, hi)))
                    t = b.tgt([[base + p["off"], base + end]],
                              f"from {base + p['off']:#x} (point {p['index']})")
                    kind = p["kind"] if isinstance(p["kind"], str) else next(iter(p["kind"]))
                    eid = f"seg/{fname}/{p['index']}"
                    b.edges.append({"id": eid, "kind": "semantic", "point": p["index"], "line": p["line"],
                                    "point_kind": kind, "function": fname, "source": [s], "target": [t]})
                    k = p["index"]
                    obligations.append(ob(f"edge/{k}", "edge", f"{X}.edge_{k}" if proved else None,
                                          eid, k, p["line"]))
                    obligations.append(ob(f"point/{k}", "point",
                                          f"CompilesToExamples.{cname}.{opt}.{fname}_point_{k}", eid, k, p["line"]))
                if pts:
                    model = f"CompilesToExamples.{cname}"
                    compact = (name, fname) in (("straight", "add3"), ("branch", "max2"))
                    compact_ns = "CompilesToExamples.Explorer.Compact"
                    if compact:
                        lean_vars["compact"] = f"{compact_ns}.{fname}"
                    stages = cx.frontend_stages("c-function-x86", lean_vars)
                    obligations += [
                        ob("translation", "translation", f"{X}.translation" if proved else None),
                        ob("mapping", "mapping", f"{X}.mapping_valid" if proved else None),
                        ob("refinement", "refinement", f"{X}.refines_dwarf"),
                        ob("abi", "abi", f"{X}.abi"),
                        ob("nonvacuity", "nonvacuity", f"{X}.inhabited"),
                        ob("elaboration", "elaboration", f"{X}.elaboration"),
                        ob("core_elaboration", "core_elaboration", f"{model}.elab_eq"),
                        ob("decoding", "decoding", f"{X}.decoding"),
                        ob("artifact", "artifact", f"CompilesToExamples.Explorer.{name}_{opt}_code"),
                        ob("nonvacuity/canonical", "nonvacuity_canonical", f"{X}.canonical" if proved else None),
                        ob("nonvacuity/universal", "nonvacuity_universal", None),
                    ]
                    lean = {"family": "c-function-x86", "vars": lean_vars,
                            "modules": [LEAN_MODULE, "CompilesToExamples.Explorer.Code", f"{PROBE}.Defs"],
                            "bindings": list(cx.model_bindings("c-function-x86", lean_vars).items()),
                            "definitions": [f"{model}.{part}" for part in ("cText", "ail", "core", "elab_eq")] +
                                           [stage["model"] for stage in stages],
                            "registry": {"source": f"silmaril.compiles_to.{name}.source",
                                         "target": f"silmaril.compiles_to.{name}.{opt.lower()}.object"}}
                    if compact:
                        lean["modules"].append(f"{compact_ns}.Checks")
                        lean["definitions"] += [lean_vars["compact"],
                                               "Silmaril.Compiler.C.Compact.ExprProjection.eval_eq"]
                        obligations.append(ob("compact_projection", "compact_projection",
                                              f"{compact_ns}.{fname}_project"))
                    ctx = {
                        "source_model": {"family": "cerberus-core",
                                         "decl": "Silmaril.Project.CompilesTo.FnData.source",
                                         "version": "Lean port of Cerberus Core (Project.Shapes.C.ElabAil, LP64)"},
                        "target_model": {"family": "x86-64", "decl": "Silmaril.X86.Open.isa",
                                         "version": "silmaril open x86-64 model (SegVC, single thread)"},
                        "abi": {"id": "sysv-amd64-integer",
                                "decl": "Silmaril.Project.CompilesTo.FnData.Holds (PointKind.entry)",
                                "version": "System V AMD64 psABI: INTEGER-class arguments, LP64"},
                        "mapping_relation": {"family": "cut-point",
                                             "decl": "Silmaril.Project.CompilesTo.FnData.mapping",
                                             "version": "c-tv program points"},
                        "comorphism": {"family": "observation", "decl": "Silmaril.Project.CompilesTo.dwarf",
                                       "version": "C objects at their DWARF DW_OP_fbreg frame slots"},
                    }
                else:
                    compact = False
                    stages = []
                    reason = unsupported_reason or "c-tv produced no program points for this function"
                    for k in ["translation", "mapping", "refinement", "abi", "nonvacuity"]:
                        obligations.append({"id": k, "kind": k, "decl": None, "statement": None,
                                            "unsupported": reason})
                    lean = {"family": None, "modules": []}
                    ctx = {"source_model": None, "target_model": None, "abi": None,
                           "mapping_relation": None, "comorphism": None}
                listing_map = [[o, o + n, s, e] for (o, n, s, e) in rows]
                out.append({
                    "schema": SCHEMA,
                    "id": f"compiles-to/{name}/{opt}/{fname}",
                    "title": f"{name}.c, gcc 13.3.0 -{opt}, {fname} (object code)",
                    "direction": "compiled",
                    "artifacts": {**{"source": src_ref, "target": obj_ref, "listing": lst_ref,
                                  "receipt": file_ref(receipt_path, "application/json"),
                                  "listing_receipt": file_ref(LISTINGS / name / opt / "RECEIPT.json",
                                                              "application/json"),
                                  "dwarf_extract": file_ref(COMPILES_TO / name / "correspondence.json", "application/json"),
                                  "include_search": file_ref(ENV / f"compiles-to-{opt}.search.json", "application/json"),
                                  "macros": file_ref(ENV / f"compiles-to-{opt}.macros.txt", "text/x-c")},
                                  **({"decoded": file_ref(LISTINGS / name / opt / "decoded.txt", "text/plain"),
                                      **frontend_artifacts(COMPILES_TO / name)}
                                     if pts else {}),
                                  **({"compact": file_ref(COMPILES_TO / name / "compact.sexp", "text/x-lisp"),
                                      "compact_origins": file_ref(COMPILES_TO / name / "compact-origins.sexp", "text/x-lisp")}
                                     if compact else {})},
                    "view": {"source": "source", "target": "listing", "target_map": listing_map,
                             "alternatives": {
                                 "source": [{"role": "source", "label": "C source"}]
                                 + (frontend_alternatives() if pts else [])
                                 + ([{"role": "compact", "label": "Compact C (signed int)"}] if compact else []),
                                 "target": [{"role": "listing", "label": "objdump (unverified)"},
                                            {"role": "target", "label": "Raw ELF bytes"}]
                                 + ([{"role": "decoded", "label": "Lean decoder listing"}] if pts else [])}},
                    "problem_form": "semantic" if pts else "relation",
                    "relation": ({"semantics": "stated", "description": "the deterministic C/x86-64 compilation problem of FnData"}
                                 if pts else {"semantics": "none",
                                              "description": "gcc 13.3.0 compiled this C to this object (receipt); "
                                                             "no Lean statement relates them"}),
                    "stages": stages + [
                        {"side": "target", "name": "objdump -d (binutils 2.40)", "trust": "trusted",
                         "input": "target", "output": "listing", "evidence": "receipt only"},
                    ] + ([{"side": "target", "name": "Lean x86 decoder (Silmaril.X86.Ext.decode)", "trust": "verified",
                           "input": "target", "output": "decoded", "obligation": "decoding",
                           "evidence": "function bytes, not an ELF parser; decodesAs checks the listing's Lean value"}]
                         if pts else []),
                    "include_env": include_env(src, ENV / f"compiles-to-{opt}.search.json", receipt),
                    "dwarf_extraction": {"input": "target", "output": "dwarf_extract", "profile": opt,
                                         "function": fname, "tool": "c-tv (gimli)", "trust": "trusted"},
                    "dwarf_facts": dwarf_facts(fn, base, bool(pts)),
                    "derivation": {"kind": "compiler", "compiler": "gcc", "version": receipt["gcc"],
                                   "image": receipt["image"], "command": receipt["command"], "opt": opt,
                                   "target": "x86_64-linux-gnu", "receipt": "receipt"},
                    "context": ctx,
                    "fragments": sorted(b.fragments.values(), key=lambda f: f["id"]),
                    "edges": b.edges,
                    "obligations": obligations,
                    "tests": [],
                    "lean": lean,
                })
                if (name, opt, fname) == ("straight", "O2", "add3"):
                    example = "CompilesToExamples.Explorer.Blocks"
                    model = "CompilesToExamples.Explorer.add3Block"
                    lean["modules"].append(example)
                    lean["definitions"].extend([model, model + "_shape"])
                    lean_vars["block_model"] = model
                    lean["bindings"] = list(cx.model_bindings("c-function-x86", lean_vars).items())
                    out[-1]["artifacts"]["block_entry"] = file_ref(
                        LISTINGS / name / opt / "block-entry.txt", "text/plain")
                    out[-1]["blocks"] = [{"side": "target", "section_range": [base, base + fn["size"]],
                        "model_base": 0x401000, "model_decl": model, "symbol": fname,
                        "decoder": "decoded", "parse": "ail", "object_obligation": "artifact",
                        "render": dict(lean["bindings"])["decoded"],
                        "attribution": [e["id"] for e in b.edges if e["kind"] == "navigation"]}]
    return out


# ---------------------------------------------------------------------------------------------
# The decompiled direction: one block of a compiled object, decompiled to C by the repository's
# decompiler (SemLift + WordC). The manifest claims no theorem about the result.

DECOMPILE = EX / "decompile"


def decompile() -> None:
    """Compile scale.c (Docker), list it, and decompile its block before `ret` (Lean)."""
    with tempfile.TemporaryDirectory() as tmp:
        cmd = ("gcc -O2 -c -fno-asynchronous-unwind-tables -fcf-protection=none -fno-ident "
               "scale.c -o /out/scale.o")
        docker([(DECOMPILE, "/src", True), (pathlib.Path(tmp), "/out", False)],
               f"{cmd}; objdump -d -w /out/scale.o > /out/listing.txt; {TOOLS}")
        t = pathlib.Path(tmp)
        obj = (t / "scale.o").read_bytes()
        (DECOMPILE / "scale.o").write_bytes(obj)
        listing = (t / "listing.txt").read_bytes().replace(b"/out/", b"")
        (DECOMPILE / "listing.txt").write_bytes(listing)
        dump(DECOMPILE / "RECEIPT.json", {
            "image": IMAGE, "workdir": "/src", "network": DOCKER_NETWORK, "command": cmd.replace("/out/", ""),
            "gcc": (t / "gcc.txt").read_text().strip(),
            "source": {"path": "scale.c", "sha256": sha256((DECOMPILE / "scale.c").read_bytes())},
            "object": {"path": "scale.o", "sha256": sha256(obj), "size": len(obj)},
            "listing": {"path": "listing.txt", "sha256": sha256(listing)},
        })
    rows = listing_rows(listing)
    block = [r for r in rows if r[0] < rows[-1][0]]  # every instruction before the final ret
    hexbytes = []
    for line in listing.decode().splitlines():
        if (m := OBJDUMP.match(line)) and int(m.group(1), 16) < rows[-1][0]:
            hexbytes += m.group(2).split()
    with tempfile.TemporaryDirectory() as tmp:
        out = pathlib.Path(tmp) / "dec.json"
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "--run",
                        "tools/compiler-explorer/decompile_block.lean", "scale", " ".join(hexbytes),
                        str(len(block)), "a=rdi,b=rsi", str(out)], cwd=ROOT, check=True)
        dec = json.loads(out.read_text())
    src = dec["source"].encode()
    (DECOMPILE / "scale.dec.c").write_bytes(src)
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    dump(DECOMPILE / "DECOMPILE.json", {
        "tool": dec["tool"], "lean_version": dec["lean_version"], "commit": commit,
        "command": ("lake env lean --run tools/compiler-explorer/decompile_block.lean scale "
                    f"'{' '.join(hexbytes)}' {len(block)} a=rdi,b=rsi OUT"),
        "input": {"path": "scale.o", "sha256": sha256(obj), "text_range": [0, rows[-1][0]],
                  "bytes": " ".join(hexbytes)},
        "checked_by_SemLift_check": dec["checked"],
        "output": {"path": "scale.dec.c", "sha256": sha256(src)},
    })
    print(f"decompiled scale: {dec['source']!r}")


def decompiled_manifests() -> list[dict]:
    d = DECOMPILE
    rec = json.loads((d / "DECOMPILE.json").read_text())
    src_ref = file_ref(d / "scale.dec.c", "text/x-c")
    obj_ref = file_ref(d / "scale.o", "application/x-elf-relocatable")
    lst = d / "listing.txt"
    rows = listing_rows(lst.read_bytes())
    b = Builder((d / "scale.dec.c").read_bytes(), src_ref["sha256"], obj_ref["sha256"], "text-offset")
    lo, hi = rec["input"]["text_range"]
    nlines = len(line_ranges((d / "scale.dec.c").read_bytes()))
    s = b.src_lines(list(range(1, nlines + 1)))
    t = b.tgt([[lo, hi]], f"[{lo:#x}, {hi:#x}): the decompiled block (the final ret is outside it)")
    b.edges.append({"id": "nav/scale/block", "kind": "navigation", "origin": "decompiler",
                    "function": "scale", "source": [s], "target": [t],
                    "note": "the decompiler's input block and its output function; not a semantic link"})
    reason = ("not stated: the decompilation obligation covers the block before ret and the C0 "
              "evaluation of the generated expression; no translation from this C text to the whole "
              "machine function (ret, the System V convention, Cerberus semantics) is stated")
    cx = cexplorer()
    vars_ = {"name": "scale", "bytes": [int(b, 16) for b in rec["input"]["bytes"].split()],
             "n": rec["input"].get("instructions", 1), "inputs": [["rdi", "a"], ["rsi", "b"]]}
    decomp = {"id": "decompilation", "kind": "decompilation",
              "decl": "CompilesToExamples.Explorer.Decompiled.scale",
              "statement": cx.statement_for("decompiled-word-block", vars_, "decompilation", None, None,
                                            (d / "scale.dec.c").read_text())}
    return [{
        "schema": SCHEMA, "id": "decompiled/scale", "direction": "decompiled",
        "title": "scale.o (gcc 13.3.0 -O2) decompiled to C by SemLift + WordC",
        "artifacts": {"source": src_ref, "target": obj_ref, "listing": file_ref(lst, "text/x-objdump"),
                      "receipt": file_ref(d / "DECOMPILE.json", "application/json"),
                      "original_source": file_ref(d / "scale.c", "text/x-c"),
                      "compile_receipt": file_ref(d / "RECEIPT.json", "application/json")},
        "view": {"source": "source", "target": "listing",
                 "target_map": [[o, o + n, s0, e0] for (o, n, s0, e0) in rows]},
        "derivation": {"kind": "decompiler", "tool": rec["tool"], "version": rec["lean_version"],
                       "commit": rec["commit"], "command": rec["command"], "receipt": "receipt",
                       "checked_by_SemLift_check": rec["checked_by_SemLift_check"]},
        "context": {"source_model": None, "target_model": None, "abi": None,
                    "mapping_relation": None, "comorphism": None},
        "fragments": sorted(b.fragments.values(), key=lambda f: f["id"]),
        "edges": b.edges,
        "obligations": [decomp] + [{"id": k, "kind": k, "decl": None, "statement": None, "unsupported": reason}
                                   for k in ("translation", "nonvacuity", "abi", "mapping", "refinement")],
        "tests": [], "lean": {"family": "decompiled-word-block", "vars": vars_,
                              "modules": ["CompilesToExamples.Explorer.Decompiled"]},
    }]


def imported_manifests() -> list[dict]:
    """sha256 compression: a C source and assembly that were both supplied (no build here)."""
    src = ROOT / "apps" / "sha256sum-min" / "inputs" / "xc_sha256.c"
    asm = ROOT / "apps" / "sha256-cli" / "src" / "sha256_compress_clang_o2.S"
    src_ref, asm_ref = file_ref(src, "text/x-c"), file_ref(asm, "text/x-asm")
    reason = ("no translation from this C source is stated: the assembly's bytes have a functional "
              "contract against a SHA-256 specification (Sha256O2.sha256_compress_O2, "
              "docs/projects/sha256sum.md), which is not a statement about this C source")
    return [{
        "schema": SCHEMA, "id": "imported/sha256-compress", "direction": "imported",
        "title": "sha256 compression: C source and clang -O2 assembly, both supplied",
        "artifacts": {"source": src_ref, "target": asm_ref},
        "view": {"source": "source", "target": "target"},
        "derivation": {"kind": "claimed",
                       "claim": ("the assembly's header says: clang 18.1.3 -O2 of xc_sha256.c, byte for "
                                 "byte, generated from Silmaril/Crypto/X86/Sha256O2/Image.lean; no "
                                 "compiler run is recorded here")},
        "context": {"source_model": None, "target_model": None, "abi": None,
                    "mapping_relation": None, "comorphism": None},
        "fragments": [], "edges": [],
        "obligations": [{"id": k, "kind": k, "decl": None, "statement": None, "unsupported": reason}
                        for k in ("translation", "nonvacuity", "abi", "mapping", "refinement")],
        "tests": [], "lean": {"family": None, "modules": []},
    }]


# ---------------------------------------------------------------------------------------------
# Rows of `sil project`: the explorer's obligations of the compiles-to builds as problem rows, so
# the project database (and its explorer page) records their statuses.

RECORDS = ROOT / "silmaril" / "compiler-explorer.toml"
ROWS = ROOT / "examples" / "compiles-to" / "CompilesToExamples" / "Explorer" / "Rows.lean"
# (file, build, function, points, namespace, segments proved)
ROW_BUILDS = [("straight", "O0", "add3", 5, "StraightO0", True), ("straight", "O2", "add3", 1, "StraightO2", True),
              ("branch", "O0", "max2", 5, "BranchO0", True), ("branch", "O2", "max2", 1, "BranchO2", False)]
# kind -> (shape, solving theorem in the build's namespace or None when it needs the segments)
ROW_KINDS = [("translation", "translation", "translation", True), ("nonvacuous", "nonvacuous", "inhabited", False),
             ("mapping", "mapping", "mapping_valid", True), ("location", "refines_location", "refines_dwarf", False)]


def row_name(name: str, opt: str, fn: str, kind: str) -> str:
    return f"silmaril.compiler_explorer.{name}.{opt.lower()}.{fn}.{kind}"


def rows(check: bool = False) -> None:
    toml = ["# GENERATED by tools/compiler-explorer/fixtures.py rows. Do not edit by hand.",
            "# The compiler explorer's obligations of the compiles-to builds as rows",
            "# (docs/projects/compiler-explorer.md), a child of the root group in silmaril/selftest.toml.",
            'schema = "silmaril.records.v0.2"', ""]
    lean = ["module", "", "-- GENERATED by tools/compiler-explorer/fixtures.py rows. Do not edit by hand.", "",
            "public import CompilesToExamples.Explorer.Builds",
            "public import CompilesToExamples.Explorer.Code", "",
            "/-! The compiler explorer's rows (`silmaril/compiler-explorer.toml`), solved by the",
            "restatements of `CompilesToExamples.Explorer.Builds`. -/", "",
            'silmaril load "silmaril/compiler-explorer.toml"', "",
            "namespace CompilesToExamples.Explorer.Rows", ""]
    children = []
    for name, opt, fn, n, ns, proved in ROW_BUILDS:
        F = f"CompilesToExamples.{name.capitalize()}.{opt}.{fn}"
        items = [(kind, shape, thm, None, needs) for kind, shape, thm, needs in ROW_KINDS]
        items += [(f"edge_{k}", "edge", f"edge_{k}", k, True) for k in range(n)]
        items += [("code", "code", None, None, False)]
        for kind, shape, thm, k, needs in items:
            row = row_name(name, opt, fn, kind)
            ok = proved or not needs
            args = f'{{ F = "{F}"' + (f", k = {k}" if k is not None else "") + " }"
            of = f"silmaril.shapes.compiler_explorer.c.{shape}.open"
            if kind == "code":
                args = (f'{{ obj = "silmaril.compiles_to.{name}.{opt.lower()}.obj", name = {{ str = "{fn}" }}, '
                        f'F = "{F}" }}')
                of = "silmaril.shapes.compiler_explorer.c.code"
            toml += ["[[instance]]", f'name = "{row}"', f'of = "{of}"',
                     f"args = {args}", f'expect = "{"THM" if ok else "OPN"}"',
                     f'title = "{fn} at {opt}: {kind.replace("_", " ")}"', ""]
            children.append(row)
            if ok:
                proof = (f"CompilesToExamples.Explorer.{name}_{opt}_code" if kind == "code"
                         else f"CompilesToExamples.Explorer.{ns}.{thm}")
                lean += [f'@[solves "{row}"] public theorem {name}_{opt.lower()}_{kind} : {row} :=',
                         f"  {proof}", ""]
    toml += ["[[group]]", 'name = "silmaril.compiler_explorer.all"',
             'title = "Compiler explorer: the compiles-to builds as compilation problems"', "children = ["]
    toml += [f'  "{c}",' for c in children] + ["]", ""]
    lean += ["end CompilesToExamples.Explorer.Rows", ""]
    if check:
        if RECORDS.read_text() != "\n".join(toml) or ROWS.read_text() != "\n".join(lean):
            raise SystemExit("error: silmaril/compiler-explorer.toml or its Rows module is not what "
                             "fixtures.py rows writes")
        return
    RECORDS.write_text("\n".join(toml))
    ROWS.write_text("\n".join(lean))
    print(f"wrote {len(children)} rows")


# ---------------------------------------------------------------------------------------------
# C => C translations of add3, and a type-error certificate

C2C = EX / "c2c"
C2C_FUNCTIONS = {
    # function: (Lean name, refuted?, what it is)
    "add3_reassoc": ("add3ReassocFn", False, "reassociation changes where signed overflow can occur; refinement open"),
    "add3_op": ("add3OpFn", False, "s - c instead of s + c; no checked counterexample recorded"),
    "add3_double": ("add3DoubleFn", True, "bug: returns (a + b + c) + (a + b + c); refuted on add3(1, 2, 3)"),
    "add3_operand": ("add3OperandFn", True, "bug: s + a instead of s + c; refuted on add3(1, 2, 3)"),
    "add3_drop": ("add3DropFn", True, "bug: returns a + b, dropping c; refuted on add3(1, 2, 3)"),
}


def function_lines(text: str, name: str) -> list[int]:
    lines = text.split("\n")
    start = next(i for i, l in enumerate(lines) if f" {name}(" in l)
    end = next(i for i in range(start, len(lines)) if lines[i].startswith("}"))
    return list(range(start + 1, end + 2))


def c2c_manifests() -> list[dict]:
    cx = cexplorer()
    src = COMPILES_TO / "straight" / "straight.c"
    tgt = C2C / "translations.c"
    src_ref, tgt_ref = file_ref(src, "text/x-c"), file_ref(tgt, "text/x-c")
    out = []
    for fn, (lean_fn, refuted, what) in C2C_FUNCTIONS.items():
        b = Builder(src.read_bytes(), src_ref["sha256"], tgt_ref["sha256"], "bytes")
        s_frag = b.src_lines(function_lines(src.read_text(), "add3"))
        tl = line_ranges(tgt.read_bytes())
        t_lines = function_lines(tgt.read_text(), fn)
        t_frag = b.tgt([list(tl[n - 1]) for n in t_lines], f"{fn}: lines {t_lines[0]}-{t_lines[-1]}")
        b.edges.append({"id": f"nav/{fn}", "kind": "navigation", "origin": "author: function to function",
                        "function": fn, "source": [s_frag], "target": [t_frag],
                        "note": "a hand-written function correspondence: no semantics"})
        vars_ = {"source_fn": "CompilesToExamples.Straight.add3Fn",
                 "target_fn": f"CompilesToExamples.Explorer.C2C.{lean_fn}"}
        stages = cx.frontend_stages("c-to-c", vars_)
        models = cx.frontend_models("c-to-c", vars_)
        refines = {"id": "translation", "kind": "c2c_refines", "decl": None,
                   "statement": cx.statement_for("c-to-c", vars_, "c2c_refines", None, None)}
        if refuted:
            refines["refutation"] = f"CompilesToExamples.Explorer.C2C.{fn.split('_', 1)[1]}_refuted"
        obligations = [refines]
        if fn == "add3_reassoc":
            obligations.append({"id": "equivalence", "kind": "c2c_equivalent", "decl": None,
                                "statement": cx.statement_for("c-to-c", vars_, "c2c_equivalent", None, None)})
        for stage in stages:
            if kind := stage.get("obligation"):
                obligations.append({"id": kind, "kind": kind, "decl": f"{models[stage['side']]}.elab_eq",
                                    "statement": cx.statement_for("c-to-c", vars_, kind, None, None)})
        out.append({
            "schema": SCHEMA, "id": f"c2c/{fn}", "direction": "imported",
            "title": f"add3 => {fn} (C => C): {what}",
            "artifacts": {"source": src_ref, "target": tgt_ref,
                          **frontend_artifacts(COMPILES_TO / "straight"), **frontend_artifacts(C2C, "target_")},
            "view": {"source": "source", "target": "target", "alternatives": {
                "source": [{"role": "source", "label": "C source"}] + frontend_alternatives(),
                "target": [{"role": "target", "label": "C translation"}] + frontend_alternatives("target_")}},
            "derivation": {"kind": "claimed", "claim": "the translations were written by hand for this fixture"},
            "problem_form": "semantic",
            "relation": {"semantics": "stated",
                         "description": "CanonicalRefines: from the canonical entries, every outcome of the "
                                        "translation is an outcome of add3 where add3 is safe"},
            "stages": stages,
            "context": {"source_model": {"family": "cerberus-core", "decl": "Silmaril.Project.Shapes.C.CFn.source",
                                         "version": "Lean port of Cerberus Core, canonical entries"},
                        "target_model": {"family": "cerberus-core", "decl": "Silmaril.Project.Shapes.C.CFn.source",
                                         "version": "Lean port of Cerberus Core, canonical entries"},
                        "abi": None, "mapping_relation": None, "comorphism": None},
            "fragments": sorted(b.fragments.values(), key=lambda f: f["id"]),
            "edges": b.edges, "obligations": obligations, "tests": [],
            "lean": {"family": "c-to-c", "vars": vars_,
                     "modules": ["CompilesToExamples.Explorer.C2C.Runs", "CompilesToExamples.Explorer.C2C.Elaborates",
                                 "CompilesToExamples.Straight.Proofs.Elaborates", f"{PROBE}.Defs"],
                     "bindings": list(cx.model_bindings("c-to-c", vars_).items()),
                     "definitions": [f"{ns}.{part}" for ns in models.values() for part in ("cText", "ail", "core")] +
                                    list(dict.fromkeys(stage["model"] for stage in stages)) +
                                    ["Silmaril.Project.Shapes.CompilesTo.CanonicalRefines",
                                     "Silmaril.Project.Shapes.CompilesTo.CanonicalEquivalent",
                                     "CompilesToExamples.Explorer.C2C.args123",
                                     "CompilesToExamples.Explorer.C2C.source_run"] +
                                    ([f"CompilesToExamples.Explorer.C2C.{fn.split('_', 1)[1]}_run"] if fn != "add3_op" else [])},
        })
    return out


def typeerror_manifests() -> list[dict]:
    cx = cexplorer()
    d = EX / "typeerror"
    src, fe, operands = d / "addp.c", d / "frontend.txt", d / "operand-types.txt"
    src_ref, operands_ref = file_ref(src, "text/x-c"), file_ref(operands, "text/plain")
    vars_ = {"t1": "Silmaril.Project.Shapes.C.intPtrCtype", "t2": "Silmaril.Project.Shapes.C.intPtrCtype"}
    b = Builder(src.read_bytes(), src_ref["sha256"], operands_ref["sha256"], "bytes")
    line = next(i + 1 for i, l in enumerate(src.read_text().split("\n")) if "p + q" in l)
    s_frag = b.src_lines([line])
    t_frag = b.tgt([[0, len(operands.read_bytes().rstrip(b"\n"))]], "the extracted operand types")
    b.edges.append({"id": "nav/addp/plus", "kind": "navigation", "origin": "author: the expression p + q",
                    "function": "addp", "source": [s_frag], "target": [t_frag],
                    "note": "the operator the restricted typing certificate is about"})
    return [{
        "schema": SCHEMA, "id": "typeerror/addp", "direction": "none",
        "title": "addp.c: does pointer + pointer typecheck?",
        "artifacts": {"source": src_ref, "target": operands_ref, "frontend": file_ref(fe, "text/plain")},
        "view": {"source": "source", "target": "target", "alternatives": {
            "target": [{"role": "target", "label": "Lean operand types"},
                       {"role": "frontend", "label": "Separate frontend diagnostic"}]}},
        "derivation": None,
        "problem_form": "judgment",
        "relation": {"semantics": "stated",
                     "description": "The exact source is recognized by AdditionFragment and violates the C11 "
                                    "6.5.6p2 additive constraint. This is not a whole-C typing judgment."},
        "stages": [{"side": "source", "name": "Restricted operand extraction", "trust": "verified", "input": "source",
                    "output": "target", "obligation": "operand_types",
                    "evidence": "Kernel equality for this text; independent of the general frontend"},
                   {"side": "source", "name": "General Lean C frontend (typing)", "trust": "evaluated", "input": "source",
                    "output": "frontend", "evidence": "#guard checks its unsupported-feature message, not a type error"}],
        "context": {"source_model": None, "target_model": None, "abi": None, "mapping_relation": None,
                    "comorphism": None},
        "fragments": sorted(b.fragments.values(), key=lambda f: f["id"]),
        "edges": b.edges,
        "obligations": [
            {"id": "typing", "kind": "typing", "decl": None,
             "refutation": "CompilesToExamples.Explorer.TypeError.addp_type_error",
             "statement": cx.statement_for("c-additive", vars_, "typing", None, None, src.read_text())},
            {"id": "operand_types", "kind": "operand_types", "decl": "CompilesToExamples.Explorer.TypeError.addp_parses",
             "statement": cx.statement_for("c-additive", vars_, "operand_types", None, None, src.read_text())}],
        "tests": [],
        "lean": {"family": "c-additive", "vars": vars_, "modules": ["CompilesToExamples.Explorer.TypeError"],
                 "definitions": ["Silmaril.Project.Shapes.C.AdditionFragment.Accepts",
                                 "Silmaril.Project.Shapes.C.AdditionFragment.operands",
                                 "CompilesToExamples.Explorer.TypeError.cText"]},
    }]


def manifests(out: pathlib.Path = MANIFESTS) -> None:
    out.mkdir(parents=True, exist_ok=True)
    for old in out.glob("*.json"):
        old.unlink()
    for m in (compiles_to_manifests() + program_manifests() + decompiled_manifests() + imported_manifests()
              + c2c_manifests() + typeerror_manifests()):
        lean = m["lean"]
        if lean["modules"]:
            names = [*lean.get("definitions", []), *lean.get("vars", {}).values()]
            names += [v["decl"].split()[0] for v in m["context"].values() if v and v.get("decl")]
            lean["definitions"] = sorted({name for name in names if isinstance(name, str) and "." in name})
        dump(out / (m["id"].replace("/", "--") + ".json"), m)
        print(f"wrote {m['id']}: {len(m['edges'])} edges, {len(m['obligations'])} obligations")


def viewer_assets(site: pathlib.Path, manifests_dir: pathlib.Path = MANIFESTS) -> None:
    """Publish exact C and ELF artifacts for the explorer's content-addressed routes."""
    cx = cexplorer()
    index = {}
    dest = site / "compiler-artifacts"
    blobs = dest / "bytes"
    blobs.mkdir(parents=True, exist_ok=True)
    for path in sorted(manifests_dir.glob("*.json")):
        manifest = json.loads(path.read_bytes())
        for role in ("source", "target"):
            ref = manifest["artifacts"][role]
            media = ref["media"]
            tab = cx.VIEWER_MEDIA.get(media)
            if tab is None:
                continue
            data = cx.read_artifact(ROOT, ref)
            sha = ref["sha256"]
            (blobs / sha).write_bytes(data)
            entry = index.setdefault(sha, {"tab": tab, "size": len(data), "paths": []})
            if entry["tab"] != tab:
                raise ValueError(f"conflicting artifact types for {sha}")
            if ref["path"] not in entry["paths"]:
                entry["paths"].append(ref["path"])
        if manifest.get("blocks"):
            inputs = {role: cx.read_artifact(ROOT, ref) for role, ref in manifest["artifacts"].items()}
            cx.check_manifest(ROOT, manifest, inputs)
            for block in cx.block_endpoints(manifest, inputs):
                index[block["elf_sha256"]].setdefault("blocks", {})[block["id"]] = {
                    **block, "problem": manifest["id"]}
    if not index:
        raise ValueError("no compiler artifacts to publish")
    dump(dest / "index.json", {"schema": cx.VIEWER_SCHEMA, "artifacts": index})


def include_map(manifest_path: pathlib.Path, out: pathlib.Path) -> None:
    """Materialize the observed filename-to-bytes map; reject any missing or mismatched bytes."""
    cx = cexplorer()
    manifest = json.loads(manifest_path.read_bytes())
    blobs = {role: cx.read_artifact(ROOT, ref) for role, ref in manifest["artifacts"].items()}
    cx.check_manifest(ROOT, manifest, blobs)
    env = manifest["include_env"]
    if env["image"] != IMAGE:
        raise ValueError("include-map supports only the fixture image digest")
    entries = env["files"]
    paths = [entry["name"] for entry in entries[1:]]
    if any(not name.startswith("/") or ".." in pathlib.PurePosixPath(name).parts or "\n" in name for name in paths):
        raise ValueError("the dependency receipt contains an invalid filename")
    data = {entries[0]["name"]: blobs["source"]}
    if paths:
        result = subprocess.run(["docker", "run", "--rm", "--platform", "linux/amd64", "--read-only",
                                 "--network", DOCKER_NETWORK,
                                 "--entrypoint", "tar", "-i", IMAGE, "-chf", "-", "--no-recursion",
                                 "--verbatim-files-from", "-T", "-"],
                                input=("\n".join(paths) + "\n").encode(), capture_output=True, check=True, timeout=120)
        with tarfile.open(fileobj=io.BytesIO(result.stdout)) as archive:
            for entry in entries[1:]:
                name = entry["name"]
                member = archive.getmember(name.lstrip("/"))
                if not member.isfile() or member.size != entry["size"]:
                    raise ValueError(f"{name}: not the recorded regular file and size")
                stream = archive.extractfile(member)
                with stream:
                    data[name] = stream.read()
                if sha256(data[name]) != entry["sha256"]:
                    raise ValueError(f"{name}: bytes differ from the recorded header SHA-256")
    dump(out, {"image": env["image"], "dependency_probe": env["dependencies"],
               "files_hex": {name: content.hex() for name, content in data.items()}})


def main(argv: list[str]) -> int:
    cmds = {"build": build, "listings": listings, "decompile": decompile, "manifests": manifests,
            "env": preprocessor_env, "stages": frontend_files,
            "rows": rows}
    if argv[1:] == ["stages", "--check"]:
        frontend_files(check=True)
        return 0
    if argv[1:] == ["rows", "--check"]:
        rows(check=True)
        return 0
    if len(argv) == 4 and argv[1] == "manifests" and argv[2] == "--out":
        manifests(pathlib.Path(argv[3]))
        return 0
    if len(argv) == 4 and argv[1] == "viewer" and argv[2] == "--out":
        viewer_assets(pathlib.Path(argv[3]))
        return 0
    if len(argv) == 4 and argv[1] == "include-map":
        include_map(pathlib.Path(argv[2]), pathlib.Path(argv[3]))
        return 0
    if len(argv) != 2 or argv[1] not in cmds:
        print(__doc__, file=sys.stderr)
        return 2
    cmds[argv[1]]()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
