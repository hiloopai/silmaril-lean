#!/usr/bin/env python3
"""Analyze and verify a build.py matrix, then write Report.md and results.json."""
import argparse
import json
from pathlib import Path
import shlex
import subprocess
import sys

from build import BASELINE, BUILDS, SOURCE, require, write_json
from verify import verify_artifacts, verify_matrix

HERE = Path(__file__).resolve().parent


def analyze(work):
    command = ["cargo", "run", "--quiet", "--locked", "--release",
               "--manifest-path", str(HERE / "Cargo.toml"), "--", str(work)]
    return json.loads(subprocess.check_output(command, text=True, encoding="utf-8"))


def num(value):
    return f"{value:,}"


def ratio(value, total):
    return f"{num(value)}/{num(total)}"


def both(value, left, right):
    return f"{ratio(value, left)} · {ratio(value, right)}"


def table(headers, rows):
    cols = "| " + " | ".join(headers) + " |"
    rule = "| " + " | ".join("---" for _ in headers) + " |"
    return "\n".join([cols, rule, *["| " + " | ".join(map(str, row)) + " |" for row in rows], ""])


def identity_rows(pairs):
    for p in pairs:
        left, right, o = (p[key] for key in ("left_denominators", "right_denominators", "overlap"))
        yield (
            f"`{p['left']}` / `{p['right']}`",
            both(o["intersecting_symbol_names"], left["symbol_names"], right["symbol_names"]),
            both(o["matched_spans"], left["total_spans"], right["total_spans"]),
            f"{left['ambiguous_spans']} / {right['ambiguous_spans']}",
            f"{left['unmatched_spans']} / {right['unmatched_spans']}",
            ratio(o["exact_spans"], o["matched_spans"]),
            ratio(o["normalized_equal_pairs"], o["normalized_eligible_pairs"]),
            num(o["normalized_equal_exact_different_pairs"]),
        )


def graph_rows(pairs):
    for p in pairs:
        left, right, o = (p[key] for key in ("left_denominators", "right_denominators", "overlap"))
        yield (
            f"`{p['left']}` / `{p['right']}`",
            ratio(o["cfg_equal_pairs"], o["cfg_eligible_pairs"]),
            both(o["intersecting_cfg_edges"], left["cfg_edges_both_eligible"], right["cfg_edges_both_eligible"]),
            both(o["intersecting_direct_call_edges"], left["direct_call_edges_both_decoded"],
                 right["direct_call_edges_both_decoded"]),
        )


def inventories(result):
    for name in BUILDS:
        b = result["builds"][name]
        i, c = b["inventory"], b["counts"]
        yield (
            f"`{name}`", num(i["defined_function_records"]), num(i["zero_size_records"]),
            num(i["usable_spans"]), num(b["usable_bytes"]), num(i["alias_spans"]), num(i["clone_spans"]),
            num(i["split_or_outline_spans"]), num(b["inline_hints"]["inline_dies"]),
            ratio(c["normalized_spans"], i["usable_spans"]),
        )


def machine_rows(result):
    for name in BUILDS:
        b = result["builds"][name]
        c = b["counts"]
        yield (
            f"`{name}`", num(c["instructions"]),
            ratio(c["cfg_spans"], b["inventory"]["usable_spans"]),
            ratio(c["unknown_direct_call_sites"], c["direct_call_sites"]),
            ratio(b["unresolved_indirect_call_sites"], c["indirect_call_sites"]),
            ratio(b["unresolved_indirect_jump_sites"], c["indirect_jump_sites"]),
            num(c["switch_table_candidates"]), num(c["lock_prefix_sites"]), num(c["mfence_sites"]), num(c["memory_xchg_sites"]),
            num(c["mutex_transfer_sites"]), num(c["compiler_helper_transfer_sites"]),
        )


def compact_sample(sample):
    c = sample["counts"]
    return (f"{num(sample['size_bytes'])} B / {num(c['blocks'])} / "
            f"{num(len(sample['direct_callees']))}")


def sample_rows(result):
    for name, a in result["builds"][BASELINE]["samples"].items():
        b = result["builds"]["clang-O2"]["samples"][name]
        if a is None or b is None:
            continue
        yield (f"`{name}`", compact_sample(a), compact_sample(b),
               "equal" if a["exact_sha256"] == b["exact_sha256"] else "different",
               ("unavailable" if a["normalized_sha256"] is None or b["normalized_sha256"] is None
                else "equal" if a["normalized_sha256"] == b["normalized_sha256"] else "different"))


def sample_notes(gcc, clang):
    lib = "sqlite3_libversion_number"
    version_bytes = gcc[lib]["short_slice_hex"]
    if version_bytes == clang[lib]["short_slice_hex"] == "b8b1992e00c3":
        yield (f"- `{lib}` has the six bytes `{version_bytes}` in both builds, "
               "a move of 3054001 into EAX followed by return.")
    length = "sqlite3_str_length"
    a, b = gcc[length]["short_slice_hex"], clang[length]["short_slice_hex"]
    if a is not None and b is not None:
        yield f"- `{length}` has bytes `{a}` in GCC and `{b}` in Clang."
    a, b = gcc["pthreadMutexEnter"], clang["pthreadMutexEnter"]
    if a and b and a["exact_sha256"] != b["exact_sha256"] and a["normalized_sha256"] is not None:
        transfers = [sample["transfer_examples"] for sample in (a, b)]
        if a["normalized_sha256"] == b["normalized_sha256"] and all(
            len(sites) == 1 and sites[0]["kind"] == "direct_exit_jump"
            and (sites[0]["destination"] or "").startswith("plt:pthread_mutex_lock@")
            for sites in transfers
        ):
            yield ("- `pthreadMutexEnter` reaches the same versioned `pthread_mutex_lock` PLT label via a "
                   "direct tail jump in both builds. The bytes differ and the normalized signatures agree.")
    a, b = gcc["sqlite3VdbeExec"], clang["sqlite3VdbeExec"]
    if a and b and a["table_examples"]:
        jump = a["table_examples"][0]["jump_address"]
        yield (f"- `sqlite3VdbeExec` has {a['counts']['switch_table_candidates']} GCC and "
               f"{b['counts']['switch_table_candidates']} Clang relative table candidates. "
               f"The first reported GCC jump is at `{jump:#x}`. The verifier independently decoded "
               "two signed table entries and checked both against GNU objdump instruction boundaries.")
    a, b = gcc["unixShmBarrier"], clang["unixShmBarrier"]
    if a and b:
        yield ("- `unixShmBarrier` has LOCK/MFENCE counts "
               f"{a['counts']['lock_prefix_sites']}/{a['counts']['mfence_sites']} in GCC and "
               f"{b['counts']['lock_prefix_sites']}/{b['counts']['mfence_sites']} in Clang. "
               "GNU objdump cross-checked both counts.")


def format_invocation(args):
    return " ".join(f'"{arg}"' if "$WORK" in arg else shlex.quote(arg) for arg in args)


def render(result):
    metadata = result["build_metadata"]
    source = metadata["source"]
    comparisons = result["comparisons"]
    cross = next(p for p in comparisons if p["left"] == BASELINE and p["right"] == "clang-O2")
    left, right, o = (cross[key] for key in ("left_denominators", "right_denominators", "overlap"))
    export_counts = {p["overlap"]["intersecting_dynamic_export_names"] for p in comparisons}
    export_summary = (f"Every pair shares {num(min(export_counts))} defined dynamic function names."
                      if len(export_counts) == 1 else
                      f"Pairs share {num(min(export_counts))} to {num(max(export_counts))} defined dynamic function names.")
    gcc = result["builds"][BASELINE]["samples"]
    clang = result["builds"]["clang-O2"]["samples"]
    checks = result["verification"]
    tool_checks = checks["primary_matrix"]

    def sum_check(key):
        return sum(row[key] for row in tool_checks.values())

    verification = (
        f"Two clean build directories agreed byte-for-byte on all {checks['replay']['files_checked']} "
        "manifested files and produced identical analyzer JSON."
        if checks["replay"] is not None else
        "This run used one build directory. A second-directory replay can be enabled with `--replay`."
    )
    parts = [
        "# SQLite 3.54.1 ELF comparison",
        "",
        "Eight x86-64 Linux SysV glibc shared-library builds compare GCC and Clang at "
        f"`-O0`, `-O1`, `-O2`, and `-O3`. The baseline is `{BASELINE}`. {export_summary}",
        "",
        f"**GCC vs. Clang at `-O2`.** Exact symbol labels give {num(o['matched_spans'])} "
        f"unambiguous pairs out of {num(left['total_spans'])} GCC spans and {num(right['total_spans'])} Clang spans. "
        f"{num(o['exact_spans'])} pairs have identical function bytes, covering {num(o['exact_bytes'])} "
        f"bytes out of {num(left['matched_bytes'])} GCC and {num(right['matched_bytes'])} Clang matched function bytes. "
        f"The normalized signatures agree in {ratio(o['normalized_equal_pairs'], o['normalized_eligible_pairs'])} "
        f"eligible pairs, including {num(o['normalized_equal_exact_different_pairs'])} with different bytes. "
        f"The CFGs share {both(o['intersecting_cfg_edges'], left['cfg_edges_both_eligible'], right['cfg_edges_both_eligible'])} "
        "typed edges among mutually eligible pairs. "
        f"The call graphs share {num(o['intersecting_direct_call_edges'])} distinct edges out of "
        f"{num(left['direct_call_edges_both_decoded'])} GCC and {num(right['direct_call_edges_both_decoded'])} "
        "Clang edges among mutually matched, decoded callers. Use these results as structural discovery evidence only.",
        "",
        "## Provenance and replay",
        "",
        f"- SQLite source ID `{source['sqlite_source_id']}`. "
        "[Upstream release](https://sqlite.org/releaselog/3_54_1.html) · "
        f"[Pinned amalgamation ZIP]({source['url']})",
        f"- ZIP SHA-256 `{source['archive_sha256']}`. ZIP SHA3-256 `{source['archive_sha3_256']}`.",
        f"- `sqlite3.c` SHA-256 `{source['sqlite3.c']}`. `sqlite3.h` SHA-256 `{source['sqlite3.h']}`.",
        f"- {metadata['tools']['gcc']} and {metadata['tools']['clang']}. "
        f"{metadata['tools']['gnu_ld']}, {metadata['tools']['glibc']}, and "
        f"{result['analyzer_tools']['rustc']}.",
        "- The amalgamation builds with fixed SQLite options and `-fno-builtin` on both drivers. "
        "Explicit compiler built-ins in the source and compiler predefines follow the selected compiler. "
        "Each run records the full sorted preprocessor dump and its SHA-256. Runtime compile options agree "
        "across the matrix after removing the compiler identification string.",
        "- Each object links twice. `libsqlite3.so` is the ordinary unstripped link. "
        "`stripped.so` comes from that link via GNU `strip --strip-all`. "
        "`relocs.so` comes from a link with `--emit-relocs` and supplies the retained text relocations. "
        "All three agree on executable load segment addresses, sizes and hashes, dynamic symbol records after "
        "resolving section indices, dynamic linking metadata and loader relocations. The runtime pair shares a build ID. "
        "The analysis link carries its own build ID and agrees with the ordinary link on usable symbol slices.",
        "- SONAME `libsqlite3.so.0` and DT_NEEDED entries `"
        + "`, `".join(tool_checks[BASELINE]["needed"]) + "` for the baseline. JSON records each build.",
        "",
        "The baseline commands run in the build-specific directory under `$WORK` "
        "with `LC_ALL=C`, `TZ=UTC`, and `SOURCE_DATE_EPOCH=0`.",
        "",
        "```sh",
        *[format_invocation(args) for args in metadata["builds"][BASELINE]["commands"][:4]],
        "```",
        "",
        "The standalone recipe, package versions, measurement definitions and schema are in the repository. "
        "[Generator and methodology](README.md) · [Measured data](results.json) · [JSON schema](results.schema.json)",
        "",
        "## ELF inventory",
        "",
        table(("Build", "Func records", "Zero size", "Usable spans", "Usable bytes", "Alias spans",
               "Clone labels", "Split/outline labels", "Inline DIEs", "Normalized coverage"), inventories(result)),
        "SHA-256 values for the ordinary and stripped runtime files are below. The JSON includes sizes, "
        "analysis ELF, object and macro dump digests and both build IDs.",
        "",
        table(("Build", "Ordinary SHA-256", "Stripped SHA-256"), (
            (f"`{name}`", f"`{metadata['builds'][name]['files']['libsqlite3.so']['sha256']}`",
             f"`{metadata['builds'][name]['files']['stripped.so']['sha256']}`") for name in BUILDS)),
        "## Symbol and byte overlap",
        "",
        "Each directional fraction shares a numerator and uses the left or right build as its denominator. "
        "Ambiguous and unmatched counts are ordered left then right. Exact compares complete symbol slices "
        "among unambiguous pairs. Normalized divides by pairs with a signature on both sides.",
        "",
        table(("Pair (left / right)", "Symbol names L · R", "Matched spans L · R", "Ambiguous L / R",
               "Unmatched L / R", "Exact / matched", "Normalized / eligible", "Normalized only"),
              identity_rows(comparisons)),
        f"For the `-O2` cross-compiler pair, the GCC and Clang unmatched counts are "
        f"{left['unmatched_spans']} and {right['unmatched_spans']}. "
        f"Of these, {left['unmatched_clone_hint_only']} and {right['unmatched_clone_hint_only']} have only a clone-name hint, "
        f"{left['unmatched_inline_hint_only']} and {right['unmatched_inline_hint_only']} have only a DWARF inline hint, "
        f"{left['unmatched_clone_and_inline_hint']} and {right['unmatched_clone_and_inline_hint']} have both, "
        f"and {left['unmatched_unknown']} and {right['unmatched_unknown']} have neither. "
        "These counts describe labels and debug annotations.",
        "",
        "## Control flow and direct call graph",
        "",
        "CFGs compare typed edges between address-order block ordinals and typed exits. "
        "The direct call graph uses exact-symbol matched callers and resolved target labels. "
        "Directional denominators in this table are limited to pairs eligible on both sides. "
        "The JSON also carries each build's full CFG and call-edge denominators.",
        "",
        table(("Pair (left / right)", "Equal CFG / eligible", "Shared CFG edges L · R",
               "Shared direct call edges L · R"), graph_rows(comparisons)),
        "## Machine idioms and unresolved sites",
        "",
        "Site counts cover fully decoded function spans. Each unknown column divides by all sites of the "
        "same kind in that build. GOT-labelled indirect sites still depend on dynamic binding. "
        "The switch detector recognises one relative jump-table idiom with two inspected entries. "
        "Those candidates stay unresolved in the graph. Mutex and helper columns count labelled transfers "
        "including calls and jumps. The JSON lists the observed mutex and helper target labels.",
        "",
        table(("Build", "Instructions", "CFG coverage", "Unknown direct calls", "Unresolved indirect calls",
               "Unresolved indirect jumps", "Table candidates", "LOCK prefix", "MFENCE", "Memory XCHG",
               "Mutex transfers", "Helper transfers"), machine_rows(result)),
        f"Baseline split or outline label examples include "
        + ", ".join(f"`{name}`" for name in result["builds"][BASELINE]["outline_name_examples"]) + ".",
        "",
        "## Independently checked sample",
        "",
        "Each build cell shows bytes, blocks and distinct direct callees in that order.",
        "",
        table(("Function", "GCC -O2", "Clang -O2", "Exact bytes", "Normalized"), sample_rows(result)),
        *sample_notes(gcc, clang),
        "",
        "## Verification and limits",
        "",
        f"- {verification}",
        f"- GNU readelf checked symbol counts, loader metadata, build IDs and sample text relocations. "
        f"GNU objdump checked {sum_check('gnu_objdump_slices_checked')} symbol slices and their transfer site counts. "
        f"LLVM objdump independently checked {sum_check('llvm_objdump_slices_checked')} small slices. "
        f"The verifier checked two entries in each of {sum_check('relative_table_examples_checked')} example tables "
        "and cross-checked DWARF inline DIE totals for both `-O2` builds.",
        f"- {sum_check('runtime_artifacts_checked')} ordinary and stripped ELFs passed isolated native smoke tests "
        "for version, source ID, thread-safe mode, absent external-loading APIs, file-backed mmap staying at zero, "
        "and a small SQL aggregate.",
        "- Scope is one release, one configuration, one target and one version of each compiler. "
        "The function universe depends on unstripped symbols, and linear decoding can include padding or "
        "miss code outside those symbol spans. Alias and clone labels, DWARF inline sites and calls via PLT/GOT "
        "carry compiler or dynamic-linker conventions. CFGs omit jump-table successors and approximate edges "
        "after calls as fallthrough. Data contents, interposition, provenance of optimized functions and "
        "behavioral equivalence require separate analysis.",
        "",
        "## References",
        "",
        "- [SQLite compile-time options](https://sqlite.org/compile.html) · "
        "[SQLite mmap pragma](https://sqlite.org/pragma.html#pragma_mmap_size)",
        "- [AMD64 System V ABI](https://gitlab.com/x86-psABIs/x86-64-ABI) · "
        "[ELF generic ABI](https://gabi.xinuos.com/) · [DWARF 4 specification](https://dwarfstd.org/dwarf4std.html)",
        "- [Rust object](https://docs.rs/object/0.36.7/object/) · "
        "[iced-x86](https://docs.rs/iced-x86/1.21.0/iced_x86/) · [gimli](https://docs.rs/gimli/0.31.1/gimli/)",
        "- [GNU readelf](https://sourceware.org/binutils/docs/binutils/readelf.html) · "
        "[GNU objdump](https://sourceware.org/binutils/docs/binutils/objdump.html) · "
        "[LLVM objdump](https://llvm.org/docs/CommandGuide/llvm-objdump.html)",
    ]
    return "\n".join(parts) + "\n"


def manifest(work):
    metadata = json.loads((work / "build.json").read_text())
    require(metadata["baseline"] == BASELINE and all(metadata["source"][key] == expected
            for key, expected in SOURCE.items()), "source or baseline manifest")
    verify_artifacts(work, metadata)
    return metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("work", type=Path, help="completed build.py directory")
    parser.add_argument("out", type=Path, help="new report directory")
    parser.add_argument("--replay", type=Path, help="second independently built directory")
    args = parser.parse_args()
    work = args.work.resolve()
    metadata = manifest(work)
    analysis = analyze(work)
    checked = verify_matrix(work, metadata, analysis)
    replay = None
    if args.replay is not None:
        second = args.replay.resolve()
        require(not work.samefile(second), "replay requires a different work directory")
        require(metadata == manifest(second), "independent build manifest differs")
        for build, record in metadata["builds"].items():
            for filename in record["files"]:
                require((work / build / filename).read_bytes() == (second / build / filename).read_bytes(),
                        f"{build}: {filename} differs between build directories")
        require(analysis == analyze(second), "independent analyzer result differs")
        replay = {"files_checked": sum(len(b["files"]) for b in metadata["builds"].values()),
                  "analysis_identical": True}
    result = {
        **analysis,
        "build_metadata": metadata,
        "analyzer_tools": {tool: subprocess.check_output([tool, "--version"], text=True).strip()
                           for tool in ("rustc", "cargo")},
        "verification": {"primary_matrix": checked, "replay": replay},
    }
    report = render(result)
    args.out.mkdir()
    write_json(args.out / "results.json", result)
    (args.out / "Report.md").write_text(report)


if __name__ == "__main__":
    try:
        main()
    except (subprocess.CalledProcessError, ValueError) as error:
        sys.exit(getattr(error, "output", None) or str(error))
