#!/usr/bin/env python3
"""Build the SQLite source/dependency atlas and write measured artifacts."""
import argparse
from bisect import bisect_right
from collections import Counter, defaultdict
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tempfile
import urllib.request
from zipfile import ZipFile

from classify import GENERATED, PRIORITIES, REGION_BY_SECTION, propagate


ROOT = Path(__file__).resolve().parent
VERSION = "3.54.1"
SOURCE_ID = "2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76"
ARCHIVES = {
    "sqlite-amalgamation-3540100": "92281c86e2957f9b9305890f9ac04204caa7b677cc868dc326d942689df28e30",
    "sqlite-src-3540100": "877c6f4996ce7adb368686bce21638de9e3d91534832ad3d9d119037d1bc22ad",
    "sqlite-preprocessed-3540100": "77320e1ed40b7e655f27b97bff9010b3f159800eddfc4f28b9d96254d8a5bd17",
}
UNIT = "sqlite3.c"
TARGET = "x86_64-linux-gnu"
CFLAGS = [
    "-std=gnu11", "-O2", "-fPIC", "-pthread", "-DSQLITE_THREADSAFE=1",
    "-DSQLITE_OMIT_LOAD_EXTENSION=1", "-DSQLITE_MAX_MMAP_SIZE=0",
]
PROBES = {"assert", "testcase", "ALWAYS", "NEVER"}
MARKER = re.compile(r"/\*+ (Begin file|End of) (\S+) \*+/")
SAMPLES = (
    "sqlite3VarintLen", "sqlite3Get4byte", "sqlite3Put4byte", "sqlite3GetToken",
    "keywordCode", "sqlite3Parser", "sqlite3VdbeSerialGet", "sqlite3VdbeExec",
    "lengthFunc", "sqlite3BtreePayload", "sqlite3PagerGet", "sqlite3OsRead",
    "sqlite3_mutex_enter", "posixIoFinderImpl", "sqlite3_sourceid",
)


def run(args, work=ROOT):
    env = dict(os.environ, LC_ALL="C")
    return subprocess.run(args, cwd=work, env=env, check=True, stdout=subprocess.PIPE).stdout


def upstream_url(stem):
    return f"https://sqlite.org/2026/{stem}.zip"


def archive(stem, cache):
    path = cache / f"{stem}.zip"
    if not path.exists():
        # Publish a cache entry only after the digest has been verified.
        with urllib.request.urlopen(upstream_url(stem), timeout=60) as response:
            contents = response.read()
        if hashlib.sha3_256(contents).hexdigest() != ARCHIVES[stem]:
            raise ValueError(f"download digest mismatch for {stem}")
        with tempfile.NamedTemporaryFile(dir=cache, delete=False) as pending:
            pending.write(contents)
        Path(pending.name).replace(path)
    if hashlib.sha3_256(path.read_bytes()).hexdigest() != ARCHIVES[stem]:
        raise ValueError(f"cached archive digest mismatch: {path}")
    return ZipFile(path)


def members(bundle, stem):
    return {
        name.removeprefix(stem + "/")
        for name in bundle.namelist()
        if name.startswith(stem + "/") and not name.endswith("/")
    }


def prepare(work, cache):
    amalgamation, source, staged = ARCHIVES
    with archive(amalgamation, cache) as bundle:
        for name in (UNIT, "sqlite3.h"):
            (work / name).write_bytes(bundle.read(f"{amalgamation}/{name}"))
    with archive(source, cache) as tree:
        source_paths = members(tree, source)
        manifest = tree.read(f"{source}/manifest.uuid").decode().strip()
        if manifest != SOURCE_ID.split()[-1]:
            raise ValueError("source tree and pinned Fossil identity disagree")
    with archive(staged, cache) as bundle:
        staged_paths = members(bundle, staged)
    source_id = re.search(rb'^#define SQLITE_SOURCE_ID +"([^"]+)"', (work / UNIT).read_bytes(), re.M)
    if not source_id or source_id[1].decode() != SOURCE_ID:
        raise ValueError("amalgamation and pinned Fossil identity disagree")
    provenance = {
        "version": VERSION,
        "fossil_source_id": SOURCE_ID,
        "archives": [{"url": upstream_url(stem), "sha3_256": digest} for stem, digest in ARCHIVES.items()],
        "inputs_sha256": {
            name: hashlib.sha256((work / name).read_bytes()).hexdigest() for name in (UNIT, "sqlite3.h")
        },
    }
    return provenance, source_paths, staged_paths


class Origins:
    def __init__(self, work, source_paths, staged_paths):
        by_basename = defaultdict(list)
        for path in sorted(source_paths):
            by_basename[PurePosixPath(path).name].append(path)
        self.ranges = {}
        self.lines = [None]  # Positions from Clang are one-based.

        def register(line, label, parents, region=None):
            identity = f"section:{line}:{label}"
            candidates = by_basename[label]
            inputs = GENERATED.get(label, ())
            if missing := set(inputs) - source_paths:
                raise ValueError(f"missing documented generator inputs: {sorted(missing)}")
            region = region or REGION_BY_SECTION.get(label)
            self.ranges[identity] = {
                "label": label,
                "stack": [self.ranges[parent]["label"] for parent in parents] + [label],
                "region": region or "Unclassified",
                "classification_confidence": "high" if region else "low",
                "staged_file": label if label in staged_paths else None,
                "source_path_candidates": candidates,
                "generator_inputs": list(inputs),
                "origin_confidence": (
                    "generated_section" if inputs else
                    "unique_basename" if len(candidates) == 1 else
                    "ambiguous_basename" if candidates else "section_only"
                ),
                "namespace": (
                    f"sqlite:generated/{label}" if inputs else
                    f"sqlite:{candidates[0]}" if len(candidates) == 1 else
                    f"sqlite:amalgamation/{label}"
                ),
            }
            return identity

        stack = []
        for line_number, line in enumerate((work / UNIT).read_text().split("\n"), 1):
            marker = MARKER.fullmatch(line)
            if marker and marker[1] == "Begin file":
                label = marker[2]
                identity = register(line_number, label, stack)
                self.ranges[identity]["begin_marker_line"] = line_number
                stack.append(identity)
            origin = stack[-1] if stack else None
            if not stack and line.startswith("SQLITE_API const char *sqlite3_sourceid(void){"):
                # mksqlite3c.tcl appends the source ID outside the embedded files.
                origin = register(line_number, UNIT, (), "Connection and public API")
                self.ranges[origin]["generated_trailer_line"] = line_number
            self.lines.append(origin)
            if marker and marker[1] == "End of" and not (marker[2] == UNIT and not stack):
                if not stack or self.ranges[stack[-1]]["label"] != marker[2]:
                    raise ValueError(f"unbalanced amalgamation marker at line {line_number}")
                self.ranges[stack.pop()]["end_marker_line"] = line_number
        if stack:
            raise ValueError("unfinished amalgamation sections")

    def at(self, location):
        if location and location["file"] == UNIT:
            return self.lines[location["line"]]
        return None

    def header(self, location):
        if not location:
            return None
        origin = self.at(location)
        if origin and self.ranges[origin]["label"].endswith(".h"):
            return origin
        if location["file"] != UNIT and location["file"].endswith(".h"):
            return "system:" + location["file"]
        return None


def profile(work, clang, cc):
    if os.uname().sysname != "Linux" or os.uname().machine != "x86_64":
        raise ValueError("the reference profile requires native x86-64 Linux")
    gcc_target = run([cc, "-dumpmachine"]).decode().strip()
    if gcc_target != TARGET or b"Free Software Foundation" not in run([cc, "--version"]):
        raise ValueError("the reference profile requires native x86-64 Linux GCC")
    clang_flags = [f"--target={TARGET}", *CFLAGS]
    macros = {}
    for label, compiler, flags in (("clang", clang, clang_flags), ("gcc", cc, CFLAGS)):
        preprocessed = run([compiler, *flags, "-E", UNIT], work)
        full_macros = sorted(run([compiler, *flags, "-dM", "-E", UNIT], work).decode().splitlines())
        active = dict(re.findall(
            r"^#define (SQLITE_THREADSAFE|SQLITE_MAX_MMAP_SIZE|SQLITE_OMIT_LOAD_EXTENSION|"
            r"NDEBUG|SQLITE_DEBUG|SQLITE_SYSTEM_MALLOC|SQLITE_MUTEX_PTHREADS|"
            r"SQLITE_OS_UNIX|SQLITE_ENABLE_FTS5|SQLITE_ENABLE_RTREE) (.*)$",
            "\n".join(full_macros), re.M,
        ))
        expected = {
            "NDEBUG": "1", "SQLITE_MAX_MMAP_SIZE": "0", "SQLITE_OMIT_LOAD_EXTENSION": "1",
            "SQLITE_OS_UNIX": "1", "SQLITE_THREADSAFE": "1",
        }
        if not expected.items() <= active.items() or "SQLITE_DEBUG" in active:
            raise ValueError(f"unexpected {label} profile macros: {active}")
        body = re.search(rb"\bsqlite3Get4byte\([^;\n]*\)\s*\{([^}]*)\}", preprocessed)
        if body is None:
            raise ValueError(f"sqlite3Get4byte body missing from {label} preprocessed output")
        macros[label] = {
            "reported_version": run([compiler, "--version"]).decode().splitlines()[0],
            "flags": flags,
            "preprocessed_sha256": hashlib.sha256(preprocessed).hexdigest(),
            "final_macro_list_sha256": hashlib.sha256("\n".join(full_macros).encode()).hexdigest(),
            "selected_final_macros": active,
            "sqlite3Get4byte_source_branch": (
                "memcpy_and_bswap" if b"__builtin_bswap32" in body[1] and b"memcpy(" in body[1]
                else "byte_subscripts" if b"p[0]" in body[1] else "other"
            ),
        }

    shutil.copyfile(ROOT / "smoke.c", work / "smoke.c")
    run([cc, *CFLAGS, "-Werror", "-c", UNIT, "-o", "sqlite3.o"], work)
    run([cc, *CFLAGS, "-Wall", "-Wextra", "-Werror", "smoke.c", "sqlite3.o", "-lm", "-o", "smoke"], work)
    run(["./smoke"], work)
    defined = {line.split()[-1] for line in run(["nm", "-g", "--defined-only", "sqlite3.o"], work).decode().splitlines()}
    if defined & {"sqlite3_load_extension", "sqlite3_enable_load_extension"}:
        raise ValueError("GCC profile unexpectedly defines load-extension API")
    return {
        "target": TARGET,
        "libc": os.confstr("CS_GNU_LIBC_VERSION"),
        "gcc_smoke": "passed",
        "gcc_load_extension_symbols": "absent",
        "compilers": macros,
    }


def coord(location):
    if not location:
        return None
    return (location["file"], location["offset"])


def body_macros(functions, macros, range_field):
    # SQLite has file-scope functions, so each physical body/extent is disjoint.
    ranges = sorted(
        (row[range_field][0]["offset"], row[range_field][1]["offset"], index)
        for index, row in enumerate(functions) if row[range_field]
    )
    if any(old[1] > new[0] for old, new in zip(ranges, ranges[1:])):
        raise ValueError("overlapping physical function intervals")
    starts = [start for start, _, _ in ranges]
    owned = [[] for _ in functions]
    unowned = []
    for macro in macros:
        offset = macro["site"]["offset"]
        pos = bisect_right(starts, offset) - 1
        if pos >= 0 and offset < ranges[pos][1]:
            owned[ranges[pos][2]].append(macro)
        else:
            unowned.append(macro)
    return owned, unowned


def assertions(functions, release_macros, debug_data):
    by_position = {(coord(f["definition"]), f["name"]): f for f in functions}
    debug = debug_data["functions"]
    macro_sites = debug_data["macros"]
    debug_owned, outside = body_macros(debug, macro_sites, "body")
    for function, own in zip(functions, release_macros):
        function["assertion_probe_sites"] = {
            "release": [m for m in own if m["name"] in PROBES],
            "debug": None,
        }
    debug_only = []
    matched_debug = 0
    debug_only_definitions = []
    for row, own in zip(debug, debug_owned):
        function = by_position.get((coord(row["definition"]), row["name"]))
        if function:
            matched_debug += 1
            if row["body"] is not None:
                function["assertion_probe_sites"]["debug"] = own
        else:
            debug_only_definitions.append({**row, "probes": own})
    return {
        "probe_names": sorted(PROBES),
        "debug_function_definitions": len(debug),
        "matched_release_definitions": matched_debug,
        "debug_definitions_without_body_extent": sum(row["body"] is None for row in debug),
        "debug_only_definitions": debug_only_definitions,
        "unowned_debug_probes": outside,
        "debug_macro_expansions_by_name": dict(Counter(m["name"] for m in macro_sites)),
    }


def enrich(raw, origins, debug_rows):
    functions = raw["functions"]
    by_location = {}
    system = {
        (coord(d["location"]), d["name"]) for d in raw["system_function_definitions"]
    }
    for function in functions:
        loc = function["definition"]
        name = function["name"]
        function["id"] = f"sqlite-{VERSION}/amalgamation/{UNIT}@{loc['line']}:{loc['column']}:{name}"
        key = (coord(loc), name)
        if key in by_location:
            raise ValueError(f"duplicate definition identity: {function['id']}")
        by_location[key] = function["id"]
        origin = origins.at(loc)
        section = origins.ranges.get(origin, {})
        function.update(
            origin_id=origin,
            region=section.get("region", "Unclassified"),
            namespace=section.get("namespace", "sqlite:amalgamation"),
            classification_confidence=section.get("classification_confidence", "low"),
        )
    assigned, outside = body_macros(functions, raw.pop("macros"), "body")
    probes = assertions(functions, assigned, debug_rows)
    probes["unowned_release_probes"] = [m for m in outside if m["name"] in PROBES]

    for function, macros in zip(functions, assigned):
        function["declared_in_public_header"] = any(
            (origin := origins.at(location)) and "sqlite3.h" in origins.ranges[origin]["stack"]
            for location in [function["definition"], *function["declaration_locations"]]
        )
        header_locations = [
            *function["declaration_locations"],
            *(d["location"] for d in function["type_declarations"]),
            *(d["location"] for d in function["function_mentions"]),
            *(d["declaration"]["location"] for d in function["nonlocal_objects"].values()),
            *(m["declared_at"] for m in macros),
        ]
        function["body_macro_counts"] = dict(sorted(Counter(m["name"] for m in macros).items()))
        for call in function["calls"]:
            indirect = call.pop("indirect")
            definition = call.pop("direct_definition")
            callee = call["callee"]
            key = (coord(definition), callee["name"]) if callee else None
            if indirect:
                kind = "indirect"
            elif key in by_location:
                kind = "sqlite_definition"
                call["target_id"] = by_location[key]
            elif key in system:
                kind = "system_definition"
            elif definition:
                kind = "definition_unmatched"
            elif callee["name"].startswith(("__builtin_", "__sync_", "__atomic_")):
                kind = "compiler_intrinsic"
            elif callee["location"] and callee["location"]["file"] == UNIT:
                kind = "sqlite_declaration_only"
            elif callee["location"]:
                kind = "external_declaration"
            else:
                kind = "locationless_declaration"
            call["kind"] = kind
            if definition and kind != "sqlite_definition":
                call["definition_location"] = definition
            if callee:
                header_locations.append(callee["location"])
        function["header_dependencies"] = sorted({
            header for location in header_locations if (header := origins.header(location))
        })
    for record in raw["record_layouts"].values():
        record["origin_id"] = origins.at(record["declaration"]["location"])
    propagate(functions)
    raw["sections"] = origins.ranges
    raw["assertions"] = probes
    raw["unowned_release_macro_expansions"] = len(outside)


def measure(raw):
    functions = raw["functions"]
    regions = {f["id"]: f["region"] for f in functions}
    calls = Counter()
    callers = defaultdict(set)
    edges = defaultdict(Counter)
    pairs = set()
    for function in functions:
        for call in function["calls"]:
            kind = call["kind"]
            calls[kind] += 1
            callers[kind].add(function["id"])
            if kind == "sqlite_definition":
                edges[function["region"]][regions[call["target_id"]]] += 1
                pairs.add((function["id"], call["target_id"]))
    return {
        "sqlite_function_definitions": len(functions),
        "definitions_without_body_extent": sum(f["body"] is None for f in functions),
        "definitions_without_source_section": sum(f["origin_id"] is None for f in functions),
        "definitions_without_embedded_file_marker": sum(
            "begin_marker_line" not in raw["sections"].get(f["origin_id"], {}) for f in functions
        ),
        "ambiguous_plain_name_groups": sum(n > 1 for n in Counter(f["name"] for f in functions).values()),
        "system_function_definitions": len(raw["system_function_definitions"]),
        "locationless_function_definitions": len(raw["locationless_function_definitions"]),
        "located_function_declarations_excluding_definitions": raw["located_function_declarations"],
        "linkage": dict(Counter(f["linkage"] for f in functions)),
        "public_header_definitions": sum(f["declared_in_public_header"] for f in functions),
        "region": dict(Counter(f["region"] for f in functions)),
        "classification_confidence": dict(Counter(f["classification_confidence"] for f in functions)),
        "origin_confidence": dict(Counter(
            raw["sections"].get(f["origin_id"], {}).get("origin_confidence", "unmapped")
            for f in functions
        )),
        "namespace_count": len({f["namespace"] for f in functions}),
        "fragments": dict(Counter(f["fragment"] for f in functions)),
        "call_sites": sum(calls.values()),
        "call_sites_without_location": sum(c["site"] is None for f in functions for c in f["calls"]),
        "call_sites_by_kind": dict(calls),
        "indirect_callee_cursor_kinds": dict(Counter(
            c["callee"]["kind"] if c["callee"] else "expression_without_referenced_declaration"
            for f in functions for c in f["calls"] if c["kind"] == "indirect"
        )),
        "indirect_callee_expression_kinds": dict(Counter(
            c["callee_expression"] or "unavailable"
            for f in functions for c in f["calls"] if c["kind"] == "indirect"
        )),
        "functions_by_call_kind": {kind: len(items) for kind, items in callers.items()},
        "unique_sqlite_caller_callee_pairs": len(pairs),
        "direct_call_sites_by_region_pair": {region: dict(targets) for region, targets in edges.items()},
        "record_layouts": len(raw["record_layouts"]),
        "record_layouts_without_size": sum(r["size_bytes"] is None for r in raw["record_layouts"].values()),
        "functions_with_header_dependencies": sum(bool(f["header_dependencies"]) for f in functions),
        "inclusion_directives": len(raw["includes"]),
        "release_macros_inside_bodies": sum(sum(f["body_macro_counts"].values()) for f in functions),
        "local_tag_function_counts": dict(Counter(tag for f in functions for tag in f["local_tag_evidence"])),
        "reachable_tag_function_counts": dict(Counter(
            tag for f in functions for tag in f["reachable_callee_effect_tags"]
        )),
        "propagated_only_tag_function_counts": dict(Counter(
            tag for f in functions for tag in f["propagated_only_effect_tags"]
        )),
        "release_macro_expansions_by_name": {
            name: sum(f["body_macro_counts"].get(name, 0) for f in functions)
            + sum(m["name"] == name for m in raw["assertions"]["unowned_release_probes"])
            for name in sorted(PROBES)
        },
    }


def public_tests(source_paths):
    tests = sorted(path for path in source_paths if path.endswith((".test", ".subtest")))
    first_pass = [
        "test/varint.test", "test/tokenize.test", "test/select1.test",
        "test/func.test", "test/btree01.test", "test/pager1.test",
        "test/wal.test", "test/unixexcl.test",
    ]
    return {
        "source_id": SOURCE_ID,
        "denominator": "All .test and .subtest file paths in the public release source ZIP",
        "by_directory": dict(Counter(str(PurePosixPath(path).parent) for path in tests)),
        "by_suffix": dict(Counter(PurePosixPath(path).suffix for path in tests)),
        "total": len(tests),
        "paths": tests,
        "first_pass_matches": [path for path in first_pass if path in tests],
        "executed": False,
    }


def markdown(raw, tests):
    stats = raw["measurements"]
    release = stats["release_macro_expansions_by_name"]
    debug = raw["assertions"]
    debug_counts = debug["debug_macro_expansions_by_name"]
    compiler = raw["profile"]["compilers"]
    sample_by_name = {f["name"]: f for f in raw["functions"] if f["name"] in SAMPLES}
    lines = [
        f"# SQLite {VERSION} source and dependency atlas",
        "",
        f"The selected library translation unit contains **{stats['sqlite_function_definitions']:,} SQLite function "
        f"definitions** and **{stats['call_sites']:,} AST call sites**. "
        f"Clang tied {stats['call_sites_by_kind'].get('sqlite_definition', 0):,} sites to SQLite bodies. "
        f"{stats['call_sites_by_kind'].get('indirect', 0):,} sites are indirect with unresolved targets.",
        "",
        f"Source ID `{SOURCE_ID}`. The generator verifies the published SHA3-256 digests for the release "
        "amalgamation, full source tree and pre-amalgamation staging bundle. "
        "[SQLite downloads](https://sqlite.org/download.html) · "
        "[Release notes](https://sqlite.org/releaselog/3_54_1.html) · "
        "[Architecture](https://sqlite.org/arch.html)",
        "",
        "## Measured profile",
        "",
        f"Native `{raw['profile']['target']}`, {raw['profile']['libc']}. Shared flags "
        f"`{' '.join(CFLAGS)}`. Both preprocessors reported `NDEBUG=1`, `SQLITE_OS_UNIX=1` and "
        "the requested threading, extension and mmap settings. The GCC object passed the file-backed SQL smoke "
        "test and defined neither load-extension API entry point.",
        "",
        f"- GCC build and preprocessing with {compiler['gcc']['reported_version']}.",
        f"- AST and record layouts with {raw['compiler']}.",
        f"- Clang driver preprocessing with {compiler['clang']['reported_version']}.",
        "- Clang processed the original C with its own preprocessor. GCC and Clang preprocess independently. "
        "For example, the preprocessed `sqlite3Get4byte` body selects "
        f"`{compiler['clang']['sqlite3Get4byte_source_branch']}` with Clang and "
        f"`{compiler['gcc']['sqlite3Get4byte_source_branch']}` with GCC. "
        "The inventory describes the Clang source view. Correspondence to GCC binaries or the repository "
        "build matrix remains unverified.",
        "",
        "## Definition and call denominators",
        "",
        f"- SQLite inventory is one row per function-definition cursor in release `sqlite3.c`. "
        f"It has {stats['linkage'].get('internal', 0):,} internal and "
        f"{stats['linkage'].get('external', 0):,} external linkage definitions, and "
        f"{stats['public_header_definitions']:,} definitions declared in the embedded public header family.",
        f"- The same parse yielded {stats['system_function_definitions']:,} out-of-unit definitions, "
        f"{stats['locationless_function_definitions']:,} locationless definitions and "
        f"{stats['located_function_declarations_excluding_definitions']:,} located non-definition "
        "declaration cursors across the whole translation unit. These are excluded from the SQLite body denominator.",
        f"- SQLite definitions outside embedded markers total {stats['definitions_without_embedded_file_marker']}. "
        f"The generated trailer is mapped explicitly. Unmapped definitions total "
        f"{stats['definitions_without_source_section']}. Definitions without a physical body range total "
        f"{stats['definitions_without_body_extent']}. Plain names shared by multiple definitions total "
        f"{stats['ambiguous_plain_name_groups']}.",
        f"- Every `CallExpr` visited in those SQLite bodies contributes one site. The direct SQLite sites "
        f"form {stats['unique_sqlite_caller_callee_pairs']:,} distinct ordered caller/callee pairs "
        f"including self edges. Sites without a physical location total {stats['call_sites_without_location']}. "
        "Callers may appear in several rows below.",
        "",
        "| Call classification | Sites | Caller definitions |",
        "| --- | ---: | ---: |",
    ]
    for kind in ("sqlite_definition", "system_definition", "external_declaration", "compiler_intrinsic",
                 "sqlite_declaration_only", "locationless_declaration", "definition_unmatched", "indirect"):
        lines.append(f"| `{kind}` | {stats['call_sites_by_kind'].get(kind, 0):,} | "
                     f"{stats['functions_by_call_kind'].get(kind, 0):,} |")
    lines += ["", "## Architectural regions", "", "| Region | Definitions |", "| --- | ---: |"]
    lines.extend(f"| {region} | {count:,} |" for region, count in sorted(stats["region"].items()))
    high = stats["classification_confidence"].get("high", 0)
    lines += [
        "",
        f"Architecture confidence is high for {high:,} definitions with an explicit section-to-region mapping "
        f"and low for the remaining {len(raw['functions']) - high:,}. This estimates placement from source-file "
        "responsibility. Mixed-role functions can warrant a different assignment.",
        "",
        f"There are {stats['namespace_count']} source namespaces. "
        + ", ".join(f"`{kind}` {count:,}" for kind, count in sorted(stats["origin_confidence"].items()))
        + ".",
        "",
        "Definitions carry a release, physical file, line, column and spelling in their IDs. Nested markers identify "
        "embedded headers. Unique canonical basenames are origin candidates. Generated sections keep their generated "
        "label and list the input grammar, templates or generator scripts where identified. Source-line offsets "
        "remain physical amalgamation coordinates. The shell, inactive conditional code and separately built "
        "extensions fall outside the translation unit.",
        "",
        "Largest cross-region dependencies by direct call-site count.",
        "",
        "| Caller region | Callee region | Sites |",
        "| --- | --- | ---: |",
    ]
    edges = sorted(
        (-count, caller, callee)
        for caller, targets in stats["direct_call_sites_by_region_pair"].items()
        for callee, count in targets.items() if caller != callee
    )
    lines.extend(f"| {caller} | {callee} | {-count:,} |" for count, caller, callee in edges[:8])
    lines += [
        "",
        "## C features, layouts and effects",
        "",
        f"{stats['functions_with_header_dependencies']:,} definitions have declaration or macro evidence from an "
        f"embedded or system header. {stats['record_layouts']:,} referenced record layouts include "
        f"{stats['record_layouts_without_size']} with unavailable size. Sizes, alignment and field bit offsets "
        "are Clang values for this target. Layout references describe syntactic type usage. Included declarations, "
        "pointer parameter shapes and pointee qualifiers help identify cases for ownership review.",
        "",
        "Local tags describe evidence such as byte buffers, members, nonlocal storage and calls at allocator, "
        "VFS or locking boundaries. Reachable tags are a union over the resolved SQLite call graph. "
        "The unknown tag remains on open direct or indirect boundaries and can propagate. "
        "These tags provide source-review candidates. Observable purity, memory ownership, bounds, aliasing "
        "and synchronization properties require separate verification.",
        "",
        "| Tag | Local functions | Reachable via SQLite edges | Via callees only |",
        "| --- | ---: | ---: | ---: |",
    ]
    for tag, count in sorted(stats["local_tag_function_counts"].items()):
        lines.append(f"| `{tag}` | {count:,} | {stats['reachable_tag_function_counts'].get(tag, 0):,} | "
                     f"{stats['propagated_only_tag_function_counts'].get(tag, 0):,} |")
    lines += [
        "",
        "Fragments group local source shapes. " + ", ".join(
            f"`{key}` {count:,}" for key, count in sorted(stats["fragments"].items())
        ) + ".",
        "",
        "## Assertions and public test inventory",
        "",
        f"The release parse recorded {release['assert']:,} `assert` and {release['testcase']:,} `testcase` "
        f"macro expansions across the amalgamation. The separate `SQLITE_DEBUG=1` parse recorded "
        f"{debug_counts.get('assert', 0):,} and {debug_counts.get('testcase', 0):,} respectively. "
        f"{debug['matched_release_definitions']:,} of {len(raw['functions']):,} release definitions also had "
        "a debug definition at the same name and physical offset. Expansion counts include no-op macros in the "
        "release parse. The JSON records unowned sites and debug-only definitions separately.",
        "",
        f"The pinned public source ZIP contains {tests['total']:,} `.test` or `.subtest` paths "
        f"across {len(tests['by_directory'])} directories. First-pass test matches include "
        + ", ".join(f"`{path}`" for path in tests["first_pass_matches"]) + ". "
        "These are inventory matches. The GCC smoke ran, and the upstream test suite remains unrun.",
        "",
        "## Representative review targets",
        "",
        "| Priority | Region | Entry points | Review scope |",
        "| --- | --- | --- | --- |",
    ]
    lines.extend(f"| {number} | {area} | {samples} | {scope} |"
                 for number, area, samples, scope in PRIORITIES)
    lines += [
        "", "Physical `sqlite3.c` positions and measured local evidence for sampled definitions.", "",
        "| Function | Line | Section | Call sites | Local tags |",
        "| --- | ---: | --- | ---: | --- |",
    ]
    for name in SAMPLES:
        f = sample_by_name[name]
        label = raw["sections"][f["origin_id"]]["label"]
        tags = ", ".join(f["local_tag_evidence"]) or "—"
        lines.append(f"| `{name}` | {f['definition']['line']:,} | `{label}` | {len(f['calls']):,} | {tags} |")
    review = ROOT / "review.md"
    if review.is_file():
        lines.extend(["", review.read_text().strip()])
    return "\n".join(lines) + "\n"


def write_json(path, value, *, pretty=False):
    with path.open("w", encoding="utf-8") as handle:
        formatting = {"indent": 2} if pretty else {"separators": (",", ":")}
        json.dump(value, handle, ensure_ascii=True, sort_keys=True, **formatting)
        handle.write("\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="output directory")
    parser.add_argument("--cache", type=Path, help="persistent public archive cache (optional)")
    parser.add_argument("--clang", default="clang-19", help="Clang driver matching linked libclang")
    parser.add_argument("--gcc", default="gcc")
    args = parser.parse_args()
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="sqlite-atlas-") as temporary:
        work = Path(temporary)
        cache = args.cache.resolve() if args.cache else work
        cache.mkdir(parents=True, exist_ok=True)
        upstream, source_paths, staged_paths = prepare(work, cache)
        origins = Origins(work, source_paths, staged_paths)
        compiler_profile = profile(work, args.clang, args.gcc)
        # Use the compiler resource directory so built-in headers match the driver.
        resource = run([args.clang, "-print-resource-dir"]).decode().strip()
        clang_flags = compiler_profile["compilers"]["clang"]["flags"] + [f"-resource-dir={resource}"]
        compiler_profile["libclang_resource_dir"] = resource
        compiler_profile["debug_delta_flags"] = ["-DSQLITE_DEBUG=1"]
        bin_dir = Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target"))
        if not bin_dir.is_absolute():
            bin_dir = ROOT / bin_dir
        run(["cargo", "build", "--release", "--locked", "--target-dir", bin_dir])
        binary = bin_dir / "release" / "sqlite-atlas-extract"
        raw = json.loads(run([binary, "inventory", *clang_flags], work))
        if raw["compiler"] != compiler_profile["compilers"]["clang"]["reported_version"]:
            raise ValueError("Clang driver and linked libclang versions disagree")
        debug = json.loads(run([binary, "assertions", *clang_flags, "-DSQLITE_DEBUG=1"], work))
        raw.update(schema_version=1, upstream=upstream, profile=compiler_profile)
        enrich(raw, origins, debug)
        raw["measurements"] = measure(raw)
        tests = public_tests(source_paths)
        write_json(output / "atlas.json", raw)
        write_json(output / "public-tests.json", tests)
        write_json(output / "measurements.json", {
            "schema_version": raw["schema_version"],
            "upstream": upstream,
            "profile": compiler_profile,
            "measurements": raw["measurements"],
            "assertion_inventory": {
                "debug_macro_expansions_by_name": raw["assertions"]["debug_macro_expansions_by_name"],
                "debug_function_definitions": raw["assertions"]["debug_function_definitions"],
                "matched_release_definitions": raw["assertions"]["matched_release_definitions"],
            },
            "public_tests": {field: value for field, value in tests.items() if field != "paths"},
        }, pretty=True)
        (output / "summary.md").write_text(markdown(raw, tests), encoding="utf-8")


if __name__ == "__main__":
    main()
