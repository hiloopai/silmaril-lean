#!/usr/bin/env python3
"""Check joins, denominators and selected source observations in a generated atlas."""
from collections import Counter
import json
from pathlib import Path
import sys

output = Path(sys.argv[1])
atlas = json.loads((output / "atlas.json").read_text())
tests = json.loads((output / "public-tests.json").read_text())
aggregate = json.loads((output / "measurements.json").read_text())
stats = atlas["measurements"]
functions = atlas["functions"]
by_id = {f["id"]: f for f in functions}
sections = atlas["sections"]
layouts = atlas["record_layouts"]

assert len(by_id) == len(functions) == stats["sqlite_function_definitions"]
assert all(f["origin_id"] in sections and f["body"] for f in functions)
assert sum(stats["region"].values()) == len(functions)
sites = Counter()
edges = set()
for function in functions:
    assert set(function["record_layouts"]) <= layouts.keys()
    for header in function["header_dependencies"]:
        assert header.startswith("system:") or sections[header]["label"].endswith(".h")
    for call in function["calls"]:
        sites[call["kind"]] += 1
        if call["kind"] == "sqlite_definition":
            assert by_id[call["target_id"]]["name"] == call["callee"]["name"]
            edges.add((function["id"], call["target_id"]))
        else:
            assert "target_id" not in call
assert sum(sites.values()) == stats["call_sites"]
assert sites == stats["call_sites_by_kind"]
assert len(edges) == stats["unique_sqlite_caller_callee_pairs"]
assert sites["definition_unmatched"] == 0

by_name = {f["name"]: f for f in functions}
assert "pure_candidate" in by_name["sqlite3VarintLen"]["local_tag_evidence"]
assert by_name["sqlite3VarintLen"]["assertion_probe_sites"]["debug"][0]["name"] == "assert"
assert by_name["sqlite3Put4byte"]["features"]["write_subscript"] == 4
assert by_name["sqlite3Get4byte"]["parameters"][0]["pointee_declared_const"] is True
assert by_name["sqlite3Put4byte"]["parameters"][0]["pointee_declared_const"] is False
assert by_name["sqlite3GetToken"]["calls"][0]["target_id"] == by_name["keywordCode"]["id"]
assert sections[by_name["keywordCode"]["origin_id"]]["label"] == "keywordhash.h"
assert "src/parse.y" in sections[by_name["sqlite3Parser"]["origin_id"]]["generator_inputs"]
assert sections[by_name["posixIoFinderImpl"]["origin_id"]]["label"] == "os_unix.c"
assert by_name["sqlite3_sourceid"]["declared_in_public_header"]
assert "vfs" in by_name["sqlite3BtreePayload"]["propagated_only_effect_tags"]
for name, member in (
    ("sqlite3OsRead", "xRead"), ("sqlite3PagerGet", "xGet"),
    ("sqlite3_mutex_enter", "xMutexEnter"),
):
    [call] = by_name[name]["calls"]
    assert call["kind"] == "indirect" and call["callee"]["name"] == member
    assert "unknown" in by_name[name]["local_tag_evidence"]
io_methods = next(row for row in layouts.values() if row["declaration"]["name"] == "sqlite3_io_methods")
assert next(field for field in io_methods["fields"] if field["name"] == "xRead")["bit_offset"] == 128

profile = atlas["profile"]
assert profile["gcc_smoke"] == "passed"
assert profile["gcc_load_extension_symbols"] == "absent"
assert profile["compilers"]["clang"]["sqlite3Get4byte_source_branch"] == "byte_subscripts"
assert profile["compilers"]["gcc"]["sqlite3Get4byte_source_branch"] == "memcpy_and_bswap"
assert len(set(tests["paths"])) == tests["total"] == sum(tests["by_suffix"].values())
assert set(tests["first_pass_matches"]) <= set(tests["paths"])
assert aggregate["measurements"] == stats
print(f"Checked {len(functions):,} definitions, {sum(sites.values()):,} call sites and {len(tests['paths']):,} public test paths.")
