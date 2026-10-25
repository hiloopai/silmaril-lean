#!/usr/bin/env python3
"""Benchmark fresh native CLI processes on original Binaryen v133 module inputs.

Samples are chosen by input size before either implementation is run. This is
module-input acceptance and output-validity measurement, not WAST test, semantic,
pass, optimization-quality or golden-output parity. Only Python's stdlib is used.
"""
import argparse
import datetime
import hashlib
import json
import os
import platform
import re
import shlex
import statistics
import subprocess
import time
from collections import Counter
from pathlib import Path

PIN = "fba5005a132d85d578be5bd010e0487ed8e2ce3e"
TOOLS = ("as", "dis", "opt-none", "opt-O2", "opt-O3", "merge")


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def invoke(command, environment, timeout):
    started = time.perf_counter_ns()
    try:
        proc = subprocess.run(list(map(str, command)), env=environment,
                              capture_output=True, timeout=timeout)
        return {"elapsed_ms": (time.perf_counter_ns() - started) / 1e6,
                "returncode": proc.returncode,
                "stderr": proc.stderr.decode(errors="replace")[-1600:]}
    except subprocess.TimeoutExpired:
        return {"elapsed_ms": (time.perf_counter_ns() - started) / 1e6,
                "returncode": None, "stderr": "timeout"}


def stratified(cases, count):
    ordered = sorted(cases, key=lambda row: (row["input_bytes"], row["id"]))
    if count == 0 or len(ordered) <= count:
        return ordered
    if count == 1:
        return [ordered[len(ordered) // 2]]
    return [ordered[round(i * (len(ordered) - 1) / (count - 1))]
            for i in range(count)]


def form_head(text):
    """Read the first atom after '(', with WAT comments as token boundaries."""
    index = 1
    while index < len(text):
        if text[index].isspace():
            index += 1
        elif text.startswith(";;", index):
            end = text.find("\n", index)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("(;", index):
            depth = 1
            index += 2
            while depth and index < len(text):
                if text.startswith("(;", index):
                    depth += 1
                    index += 2
                elif text.startswith(";)", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
        else:
            break
    start = index
    while index < len(text) and not text[index].isspace() and text[index] not in '()"' and not text.startswith(";;", index):
        index += 1
    return text[start:index] or None


def top_forms(text):
    """Find exact top-level forms, respecting strings and nested WAT comments."""
    forms = []
    index = depth = 0
    start = None
    block = 0
    string = False
    while index < len(text):
        pair = text[index:index + 2]
        if block:
            if pair == "(;":
                block += 1
                index += 2
            elif pair == ";)":
                block -= 1
                index += 2
            else:
                index += 1
        elif string:
            if text[index] == "\\":
                index += 2
            elif text[index] == '"':
                string = False
                index += 1
            else:
                index += 1
        elif pair == ";;":
            end = text.find("\n", index)
            index = len(text) if end < 0 else end + 1
        elif pair == "(;":
            block = 1
            index += 2
        elif text[index] == '"':
            string = True
            index += 1
        elif text[index] == "(":
            if depth == 0:
                start = index
            depth += 1
            index += 1
        elif text[index] == ")":
            depth -= 1
            if depth < 0:
                raise ValueError("unmatched closing parenthesis")
            index += 1
            if depth == 0:
                forms.append((start, index))
        else:
            index += 1
    if depth or block or string:
        raise ValueError("unterminated parenthesis, comment or string")
    return forms


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("candidate-bin", "reference-bin", "upstream", "work", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--candidate-revision", required=True,
                        help="source revision compiled into the supplied native binaries")
    parser.add_argument("--samples", type=int, default=24,
                        help="size-stratified samples per input family; 0 selects every case")
    parser.add_argument("--max-bytes", type=int, default=262144,
                        help="exclude larger individual source modules/binaries; 0 disables the limit")
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=10)
    parser.add_argument("--tools", choices=TOOLS, nargs="+", default=list(TOOLS))
    args = parser.parse_args()
    if args.samples < 0 or args.max_bytes < 0 or args.repeats < 1 or args.timeout <= 0:
        parser.error("samples/max-bytes must be nonnegative; repeats/timeout must be positive")
    upstream = args.upstream.resolve()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=upstream, text=True).strip()
    if revision != PIN:
        parser.error("expected upstream revision " + PIN)
    if subprocess.check_output(["git", "status", "--porcelain", "--", "test"], cwd=upstream).strip():
        parser.error("upstream test tree must be clean")
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    environment = {**os.environ, "BINARYEN_CORES": "1", "LEAN_NUM_THREADS": "1"}
    bins = {"candidate": args.candidate_bin.resolve(), "reference": args.reference_bin.resolve()}
    base_tools = sorted({"opt" if tool.startswith("opt-") else tool for tool in args.tools} | {"as", "opt"})
    binaries = {str(directory / ("wasm-" + tool)): digest(directory / ("wasm-" + tool))
                for directory in bins.values() for tool in base_tools}
    versions = {}
    for name, directory in bins.items():
        for tool in base_tools:
            binary = directory / ("wasm-" + tool)
            proc = subprocess.run([str(binary), "--version"], env=environment,
                                  capture_output=True, text=True, timeout=args.timeout)
            if proc.returncode:
                parser.error(str(binary) + " --version failed")
            versions[str(binary)] = proc.stdout.strip()
            if name == "reference" and not re.search(r"\b133\b", proc.stdout):
                parser.error("reference executables must be Binaryen v133")
    def run(command):
        return invoke(command, environment, args.timeout)
    def ref(tool):
        return bins["reference"] / ("wasm-" + tool)
    def path_for(identifier, suffix):
        return work / (hashlib.sha256(identifier.encode()).hexdigest()[:24] + suffix)
    inventory, cases = [], []
    tracked = subprocess.check_output(["git", "ls-files", "-z", "test"], cwd=upstream)
    for raw in sorted(part for part in tracked.split(b"\0") if part):
        relative = Path(os.fsdecode(raw))
        if relative.suffix not in (".wat", ".wast", ".wasm"):
            continue
        path = upstream / relative
        payload = path.read_bytes()
        if relative.suffix == ".wasm":
            cases.append({"id": str(relative), "kind": "binary", "input": path,
                          "fixture_sha256": digest(path), "input_bytes": len(payload)})
            continue
        try:
            text = payload.decode("utf-8")
            spans = top_forms(text)
        except (ValueError, UnicodeDecodeError) as error:
            inventory.append({"id": str(relative), "status": "source-scan-rejected", "error": str(error)})
            continue
        module_index = 0
        for start, end in spans:
            if form_head(text[start:end]) != "module":
                continue
            identifier = f"{relative}#module-{module_index}"
            module_index += 1
            source = text[start:end].encode("utf-8")
            target = path_for(identifier, ".wat")
            target.write_bytes(source)
            cases.append({"id": identifier, "kind": "text", "input": target,
                          "fixture_sha256": digest(path), "source_character_span": [start, end],
                          "input_bytes": len(source)})
    eligible = [row for row in cases if not args.max_bytes or row["input_bytes"] <= args.max_bytes]
    text_cases = stratified([row for row in eligible if row["kind"] == "text"], args.samples)
    module_cases = stratified(eligible, args.samples)
    prepared, preparation = {}, []
    for row in {row["id"]: row for row in text_cases + module_cases}.values():
        path = row["input"]
        if row["kind"] == "text":
            path = path_for(row["id"], ".input.wasm")
            status = run([ref("as"), row["input"], "--all-features", "-o", path])
            if status["returncode"] != 0:
                preparation.append({"id": row["id"], "status": "reference-assembly-failed", "result": status})
                continue
        validation = run([ref("opt"), path, "--all-features", "-o", path_for(row["id"], ".validated.wasm")])
        if validation["returncode"] != 0:
            preparation.append({"id": row["id"], "status": "reference-validation-failed", "result": validation})
            continue
        prepared[row["id"]] = path
    jobs = [("as", row, [row["input"]], []) for row in text_cases if row["id"] in prepared]
    jobs += [(tool, row, [prepared[row["id"]]], flags)
             for tool, flags in (("dis", []), ("opt-none", []), ("opt-O2", ["-O2"]), ("opt-O3", ["-O3"]))
             for row in module_cases if row["id"] in prepared]
    merge_excluded = []
    # Read only a deliberately small recipe grammar. Never execute upstream RUN
    # directives as shell commands. Binary output replaces each recipe's -S.
    if "merge" in args.tools:
        for source in sorted((upstream / "test/lit/merge").glob("*.wat")):
            for line_number, line in enumerate(source.read_text().splitlines(), 1):
                marker = ";; RUN: wasm-merge "
                if not line.startswith(marker):
                    continue
                identifier = f"{source.relative_to(upstream)}:RUN-{line_number}"
                tokens = shlex.split(line[len(marker):].split("|", 1)[0])
                inputs, flags, reason = [], [], None
                index = 0
                while index < len(tokens):
                    token = tokens[index]
                    if token in ("-all", "--all-features", "-S"):
                        index += 1
                    elif token == "-o" and index + 1 < len(tokens):
                        index += 2
                    elif token in ("--rename-export-conflicts", "--skip-export-conflicts"):
                        flags.append(token)
                        index += 1
                    elif token in ("%s", "%s.second", "%s.third") and index + 1 < len(tokens):
                        inputs.append((Path(str(source) + token[2:]), tokens[index + 1]))
                        index += 2
                    else:
                        reason = "unsupported recipe token " + token
                        break
                if reason or not inputs:
                    merge_excluded.append({"id": identifier, "reason": reason or "no inputs"})
                    continue
                arguments, hashes, total_bytes = [], [], 0
                for path, namespace in inputs:
                    binary = path_for(str(path), ".merge-input.wasm")
                    result = run([ref("as"), path, "--all-features", "-o", binary])
                    if result["returncode"] != 0:
                        reason = "reference input assembly failed"
                        break
                    arguments += [binary, namespace]
                    hashes.append({"fixture": str(path.relative_to(upstream)), "namespace": namespace,
                                   "fixture_sha256": digest(path), "binary_sha256": digest(binary)})
                    total_bytes += binary.stat().st_size
                if reason:
                    merge_excluded.append({"id": identifier, "reason": reason})
                    continue
                jobs.append(("merge", {"id": identifier, "input_bytes": total_bytes,
                                       "merge_inputs": hashes}, arguments, flags))
    outcomes = []
    load = lambda: Path("/proc/loadavg").read_text().strip() if Path("/proc/loadavg").exists() else None
    start_load = load()
    for tool, row, inputs, flags in jobs:
        if tool not in args.tools:
            continue
        base = "opt" if tool.startswith("opt-") else tool
        outputs = {name: path_for(tool + row["id"], "." + name + (".wat" if base == "dis" else ".wasm"))
                   for name in bins}
        for path in outputs.values():
            path.unlink(missing_ok=True)
        commands = {name: [directory / ("wasm-" + base), *inputs, *flags,
                          *(["--all-features"] if name == "reference" else []), "-o", outputs[name]]
                    for name, directory in bins.items()}
        warmups = {name: run(command) for name, command in commands.items()}
        runs = {name: [] for name in bins}
        for repeat in range(args.repeats):
            for name in (("candidate", "reference") if repeat % 2 == 0 else ("reference", "candidate")):
                if warmups[name]["returncode"] == 0:
                    outputs[name].unlink(missing_ok=True)
                    runs[name].append(run(commands[name]))
        result = {"tool": tool, **{key: value for key, value in row.items() if key != "input"},
                  "input_sha256": [digest(path) for path in inputs if isinstance(path, Path)],
                  "commands": {name: list(map(str, command)) for name, command in commands.items()},
                  "warmup": warmups, "runs": runs, "outputs": {}}
        for name, path in outputs.items():
            statuses = [warmups[name], *runs[name]]
            if any(status["returncode"] is None for status in statuses):
                output = {"status": "timeout"}
            elif any(status["returncode"] != 0 for status in statuses):
                output = {"status": "rejected"}
            elif not path.exists():
                output = {"status": "missing-output"}
            else:
                checked = path
                if base == "dis":
                    checked = path.with_suffix(".reassembled.wasm")
                    assembly = run([ref("as"), path, "--all-features", "-o", checked])
                    if assembly["returncode"] != 0:
                        result["outputs"][name] = {"status": "invalid-text", "validation": assembly}
                        continue
                validation = run([ref("opt"), checked, "--all-features", "-o", work / "validation.wasm"])
                output = {"status": "valid" if validation["returncode"] == 0 else "invalid",
                          "bytes": path.stat().st_size, "sha256": digest(path)}
                if validation["returncode"] != 0:
                    output["validation"] = validation
            result["outputs"][name] = output
        if all(value["status"] == "valid" for value in result["outputs"].values()):
            result["median_ms"] = {name: statistics.median(run["elapsed_ms"] for run in repetitions)
                                   for name, repetitions in runs.items()}
        outcomes.append(result)
        print(json.dumps({"tool": tool, "id": row["id"], "outputs": result["outputs"],
                          "median_ms": result.get("median_ms")}), flush=True)
    summary = {}
    for tool in args.tools:
        selected = [row for row in outcomes if row["tool"] == tool]
        reference_valid = [row for row in selected if row["outputs"]["reference"]["status"] == "valid"]
        paired = [row for row in selected if "median_ms" in row]
        totals = {name: sum(row["median_ms"][name] for row in paired) for name in bins}
        summary[tool] = {"selected": len(selected), "reference_valid": len(reference_valid),
                         "candidate_valid_on_reference_valid": sum(row["outputs"]["candidate"]["status"] == "valid" for row in reference_valid),
                         "candidate_statuses": dict(Counter(row["outputs"]["candidate"]["status"] for row in selected)),
                         "valid_pairs": len(paired), "sum_per_case_median_ms": totals,
                         "candidate_over_reference": totals["candidate"] / totals["reference"] if paired else None,
                         "paired_output_bytes": {name: sum(row["outputs"][name]["bytes"] for row in paired) for name in bins}}
    report = {"schema_version": 1, "measured_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "harness_sha256": digest(Path(__file__)), "candidate_revision": args.candidate_revision,
              "upstream_revision": revision, "host": {"platform": platform.platform(), "machine": platform.machine(),
              "cpu": next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
                           if line.startswith("model name")), "unknown") if Path("/proc/cpuinfo").exists() else "unknown"},
              "scope": "original top-level modules/binaries; input acceptance and output validity; no WAST assertions, semantic/golden/pass parity",
              "policy": {"samples_per_family": args.samples, "max_input_bytes": args.max_bytes,
                         "selection": "size-stratified before candidate/reference acceptance; no replacement on rejection",
                         "warmups": 1, "repeats": args.repeats, "timeout_seconds": args.timeout,
                         "BINARYEN_CORES": "1", "LEAN_NUM_THREADS": "1", "validation_outside_timing": True,
                         "merge": "all recognized positive lit/merge recipes; binary inputs/output; original order/names/conflict policies; -S removed"},
              "inventory": {"module_cases": len(cases), "eligible_cases": len(eligible),
                            "over_size_limit": len(cases) - len(eligible), "scan_errors": inventory,
                            "selected_text": [row["id"] for row in text_cases],
                            "selected_modules": [row["id"] for row in module_cases],
                            "reference_preparation_failures": preparation, "merge_excluded": merge_excluded},
              "binary_sha256": binaries, "versions": versions,
              "host_loadavg": {"start": start_load, "end": load()}, "summary": summary, "cases": outcomes}
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    # Rejections are measurements, not harness failures. Invalid output is a failure.
    return int(any(output["status"] in ("invalid", "invalid-text", "missing-output")
                   for row in outcomes for output in row["outputs"].values()))


if __name__ == "__main__":
    raise SystemExit(main())
