#!/usr/bin/env python3
"""The x86 ELF probe corpus as OSS Verify style problems (#3454, extended shapes #3610).

`problems/x86-probes.json` is the catalogue: per probe of
`examples/verification-projects/theorem-dev/lps-probes/probes` (and the memory probes, whose
data modules are in `Silmaril/Process/LPS/Probes/Data`), its statements in published shapes
(`haltsMayFail`, `haltsWithinBudget`) or extended ones (`haltsMayFailWith`, #3610), each with a
status (`proved`, `refuted`, `stated`), and the agreement statements between pairs of probes.

Commands:

* `gen`: write `Silmaril/Process/LPS/Problems/X86Probes/Corpus.lean`. Per probe it has the
  harness (`statements`, `proved`), the problem (`probeProblem`: the hub's native x86-64
  profile `Problems.nativeX86`, one build, plain), and per statement a definition in the
  published shape with its `rfl` equation `<name>_eq` against `ProfileProblem.denote` (or
  `denoteExt`, or `PairProblem.denote`), and an `Entry` with the catalogue's status. Every
  extended statement has `<name>_base`, the proved implication to its published shape.
* `check` (default): the catalogue is well formed (every probe has a fixture or a data
  module, exit sets are bytes, every status is known, every refuted entry names its reason
  `refutedBy`, the launch `domain` is stated), `Corpus.lean` is what `gen` writes,
  and the results module settles exactly the `proved` and `refuted` statements
  (`Results.results`, checked in Lean by `results_settle`).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CATALOGUE = "tools/verification-projects/problems/x86-probes.json"
CORPUS = "Silmaril/Process/LPS/Problems/X86Probes/Corpus.lean"
RESULTS = "Silmaril/Process/LPS/Problems/X86Probes/Results.lean"
DATA = "Silmaril/Process/LPS/Probes/Data"
NS = "Silmaril.Process.LPS.Problems.X86Probes"
STATUSES = ("proved", "refuted", "stated")
KINDS = ("haltsMayFail", "haltsWithinBudget", "haltsMayFailWith")


class CatalogueError(Exception):
    pass


def load(root: Path) -> dict:
    return json.loads((root / CATALOGUE).read_text())


def exits_lean(exits) -> tuple[str, str]:
    """The `ExitChoice` and the exit list of a statement."""
    if exits == "any":
        return ".any", "Exits.any"
    if exits == "okOrRefused":
        return ".okOrRefused", "Exits.okOrRefused"
    codes = ", ".join(str(c) for c in exits)
    return f"(.listed [{codes}])", f"[{codes}]"


def bytes_lean(bs: list[int]) -> str:
    return "[" + ", ".join(str(b) for b in bs) + "]"


def trace_lean(trace: dict) -> str:
    if trace.get("silent"):
        return ".silent"
    if trace.get("echo"):
        return ".echo"
    if "stdoutPrefix" in trace:
        return f"(.stdoutPrefix {bytes_lean(trace['stdoutPrefix'])})"
    if "stdoutNonemptyPrefix" in trace:
        return f"(.stdoutNonemptyPrefix {bytes_lean(trace['stdoutNonemptyPrefix'])})"
    if "stdoutPieces" in trace:
        return "(.stdoutPieces [" + ", ".join(bytes_lean(p) for p in trace["stdoutPieces"]) + "])"
    raise CatalogueError(f"unknown trace spec {trace}")


def describe_trace(trace: dict) -> str:
    if trace.get("silent"):
        return "nothing is written"
    if trace.get("echo"):
        return "stdout is a prefix of what is read from stdin"
    if "stdoutPrefix" in trace:
        return f"stdout is a prefix of {bytes(trace['stdoutPrefix'])!r}"
    if "stdoutNonemptyPrefix" in trace:
        return f"stdout is a nonempty prefix of {bytes(trace['stdoutNonemptyPrefix'])!r}"
    pieces = ", ".join(repr(bytes(p)) for p in trace["stdoutPieces"])
    return f"stdout is a prefix of each of {pieces} in turn"


def check_refutation(where: str, entry: dict, reasons: dict) -> list[str]:
    """A refuted entry names why (`refutedBy`, a key of `refutationReasons`); others do not."""
    reason = entry.get("refutedBy")
    if entry["status"] == "refuted":
        if reason not in reasons:
            return [f"{where}: refuted without a known refutedBy ({reason})"]
    elif reason is not None:
        return [f"{where}: refutedBy on a {entry['status']} entry"]
    return []


def describe_status(entry: dict, reasons: dict) -> str:
    if entry["status"] == "refuted":
        return f"refuted, {entry['refutedBy']}: {reasons[entry['refutedBy']]}"
    return entry["status"]


def validate(root: Path, cat: dict) -> list[str]:
    problems = []
    reasons = cat.get("refutationReasons", {})
    if not cat.get("domain"):
        problems.append("the catalogue does not state its launch domain")
    fixtures = root / cat["fixtures"]
    seen = set()
    for probe in cat["probes"]:
        name, data = probe["probe"], probe["data"]
        if name in seen:
            problems.append(f"{name}: listed twice")
        seen.add(name)
        if not (root / DATA / f"{data}.lean").exists():
            problems.append(f"{name}: no data module {DATA}/{data}.lean")
        fixture = fixtures / f"{name}.json"
        if fixture.exists():
            declaration = json.loads(fixture.read_text())
            outcome = declaration["expected"]["outcome"]
            for statement in probe["statements"]:
                exits = statement["exits"]
                if "exit" in outcome and isinstance(exits, list) and outcome["exit"] not in exits:
                    problems.append(f"{name}/{statement['name']}: Linux's status {outcome['exit']} "
                                    f"is outside the exit set {exits}")
        names = set()
        for statement in probe["statements"]:
            if statement["name"] in names:
                problems.append(f"{name}/{statement['name']}: listed twice")
            names.add(statement["name"])
            if statement["kind"] not in KINDS:
                problems.append(f"{name}/{statement['name']}: unknown kind {statement['kind']}")
            if statement["status"] not in STATUSES:
                problems.append(f"{name}/{statement['name']}: unknown status {statement['status']}")
            problems += check_refutation(f"{name}/{statement['name']}", statement, reasons)
            exits = statement["exits"]
            if isinstance(exits, list) and not all(isinstance(c, int) and 0 <= c < 256 for c in exits):
                problems.append(f"{name}/{statement['name']}: exit codes must be bytes")
            if statement["kind"] == "haltsMayFailWith":
                if not any(s["kind"] == "haltsMayFail" and s["exits"] == exits for s in probe["statements"]):
                    problems.append(f"{name}/{statement['name']}: no published statement with its exit set")
    for pair in cat["pairs"]:
        for side in ("first", "second"):
            if pair[side] not in seen:
                problems.append(f"{pair['name']}: {pair[side]} is not a probe")
        if pair["status"] not in STATUSES:
            problems.append(f"{pair['name']}: unknown status {pair['status']}")
        problems += check_refutation(pair["name"], pair, reasons)
        if pair["shape"] != "agrees" or pair["budgets"] != "standard":
            problems.append(f"{pair['name']}: only the plain agrees shape at the standard budgets")
    return problems


def data_of(cat: dict) -> dict[str, str]:
    return {probe["probe"]: probe["data"] for probe in cat["probes"]}


def statement_lean(statement: dict) -> str:
    choice, _ = exits_lean(statement["exits"])
    if statement["kind"] == "haltsMayFail":
        return f".haltsMayFail .plain {choice}"
    if statement["kind"] == "haltsWithinBudget":
        return f".haltsWithinBudget .plain .{statement['budgets']} {choice}"
    raise CatalogueError("not a published statement")


def gen(cat: dict) -> str:
    out = []
    w = out.append
    reasons = cat["refutationReasons"]
    w("module")
    w("")
    w(f"public import {NS}.Basic")
    for probe in cat["probes"]:
        w(f"public import Silmaril.Process.LPS.Probes.Data.{probe['data']}")
    w("")
    w("/-! # The x86 ELF probe corpus as problems (generated: do not edit)")
    w("")
    w(f"Generated by `tools/verification-projects/x86_probe_problems.py gen` from `{CATALOGUE}`.")
    w("")
    w("Each probe is a harness with one build, `plain` (its snapshot), on the hub's native x86-64")
    w("profile `Problems.nativeX86` (`probeProblem`). Every statement is a definition in the")
    w("published shape (`StatementProfile.haltsMayFail`, `StatementProfile.haltsWithinBudget`,")
    w("`StatementProfile.agrees`) or the extended one (`StatementProfile.haltsMayFailWith`, #3610),")
    w("with its `rfl` equation against `ProfileProblem.denote` (`denoteExt`, `PairProblem.denote`),")
    w("and an `Entry` carrying the catalogue's status. An extended statement implies its published")
    w("one (`<name>_base`). The proofs and refutations are in `Problems.X86Probes.Results`.")
    w("")
    w("These are `ProfileProblem` statements over `nativeX86`, not `Problem.denote?` (`Shapes`)")
    w("forms. Their domain is the hub's x86 launch envelope: every entry with")
    w("`nativeX86.validEntry` (`= X86Launch.ValidEntry`, `nativeX86_validEntry`: the stack pointer")
    w("in its window below `TASK_SIZE` and 16-aligned, the mmap base in fixed bounds, the image")
    w("below the stack reservation) and every input with `nativeX86.validInput false`")
    w("(`nativeX86_validInput`: `X86Launch.ValidInput`, which fixes `hwcap = 0`, and `abort()` not")
    w("modelled). theorem.dev's riscv64 `Run.ValidInput` (an RV64GC(V) `hwcap`, Sv48,")
    w("`ValidEntryVa`) is a different domain.")
    w("")
    w("A refuted entry's docstring names why (`refutedBy` in the catalogue). `modelCoverage`")
    w("refutations come from a call the model lacks (chaos) and refute every exit set, so they")
    w("say nothing about Linux's status; `shortWrite` refutations measure the model's short-write")
    w("semantics, not a Linux-observable difference.")
    w("-/")
    w("")
    w("@[expose] public section")
    w("set_option autoImplicit false")
    w("")
    w(f"namespace {NS}.Corpus")
    w("")
    w("open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Problems")
    w("open Silmaril.Process.LPS.Probes Silmaril.Process.LPS.Shapes")
    w("")
    entries = []
    for probe in cat["probes"]:
        name, data = probe["probe"], probe["data"]
        snap = f"Data.{data}.probe.snapshot"
        published = [s for s in probe["statements"] if s["kind"] != "haltsMayFailWith"]
        extended = [s for s in probe["statements"] if s["kind"] == "haltsMayFailWith"]
        w(f"namespace {data}")
        w("")
        w(f"/-- The published statements of `{name}`. -/")
        w("def statements : List (String × Statement) :=")
        w("  [" + ",\n   ".join(f'("{s["name"]}", {statement_lean(s)})' for s in published) + "]")
        w("")
        proved = [s["name"] for s in published if s["status"] == "proved"]
        w(f"/-- The harness of `{name}`: its statements and those proved here. -/")
        w(f'def harness : Harness := probeHarness "{name}" statements [' +
          ", ".join(f'"{n}"' for n in proved) + "]")
        w("")
        w(f"/-- `{name}` on the native x86-64 profile, one build (`plain`). -/")
        w(f"def problem : ProfileProblem X86Launch.Snapshot := probeProblem harness Data.{data}.probe")
        w("")
        for s in published:
            choice, codes = exits_lean(s["exits"])
            note = f" {s['note']}." if s.get("note") else ""
            if s["kind"] == "haltsMayFail":
                w(f"/-- `halts_may_fail {s['exits']}` ({describe_status(s, reasons)}).{note} -/")
                w(f"def {s['name']} : Prop := nativeX86.haltsMayFail {codes} {snap}")
            else:
                w(f"/-- `halts_within_budget Budgets.Standard.lim_source {s['exits']}` "
                  f"({describe_status(s, reasons)}).{note} -/")
                w(f"def {s['name']} : Prop :=")
                w(f"  nativeX86.haltsWithinBudget Budgets.{s['budgets']}.limSource {codes} {snap}")
            w("")
            w(f"theorem {s['name']}_eq : {s['name']} = problem.denote ({statement_lean(s)}) := rfl")
            w("")
            entries.append((data, s))
        for s in extended:
            choice, codes = exits_lean(s["exits"])
            spec = trace_lean(s["trace"])
            base = next(b for b in published if b["kind"] == "haltsMayFail" and b["exits"] == s["exits"])
            note = f" {s['note']}." if s.get("note") else ""
            w(f"/-- Extended (#3610): `halts_may_fail {s['exits']}`, and in every execution "
              f"{describe_trace(s['trace'])} ({describe_status(s, reasons)}).{note} -/")
            w(f"def {s['name']} : Prop :=")
            w(f"  nativeX86.haltsMayFailWith {codes} ({spec} : TraceSpec).denote {snap}")
            w("")
            w(f"theorem {s['name']}_eq :")
            w(f"    {s['name']} = problem.denoteExt (.haltsMayFailWith .plain {choice} {spec}) := rfl")
            w("")
            w(f"/-- The extended statement implies the published `{base['name']}`. -/")
            w(f"theorem {s['name']}_base (h : {s['name']}) : {base['name']} :=")
            w(f"  problem.denote_of_denoteExt (.haltsMayFailWith .plain {choice} {spec}) h")
            w("")
            entries.append((data, s))
        for s in probe["statements"]:
            w(f'def {s["name"]}_entry : Entry := ⟨"{name}", "{s["name"]}", {s["name"]}, .{s["status"]}⟩')
        w("")
        w(f"end {data}")
        w("")
    data = data_of(cat)
    w("namespace Pairs")
    w("")
    for pair in cat["pairs"]:
        first, second = data[pair["first"]], data[pair["second"]]
        note = f" {pair['note']}." if pair.get("note") else ""
        expected = f" Expected: {pair['expected']}." if pair.get("expected") and pair["status"] == "stated" else ""
        w(f"/-- `{pair['first']}` and `{pair['second']}` compared by `agrees` at the standard budgets. -/")
        w(f'def {pair["name"]}_problem : PairProblem X86Launch.Snapshot :=')
        w(f'  probePair "{pair["name"]}" Data.{first}.probe Data.{second}.probe')
        w("")
        w(f"/-- `agrees Budgets.Standard.lim_source Budgets.Standard.lim_target` "
          f"({describe_status(pair, reasons)}).{note}{expected} -/")
        w(f"def {pair['name']} : Prop :=")
        w(f"  StatementProfile.agrees nativeX86 nativeX86 Budgets.standard.limSource Budgets.standard.limTarget")
        w(f"    Data.{first}.probe.snapshot Data.{second}.probe.snapshot")
        w("")
        w(f"theorem {pair['name']}_eq : {pair['name']} = {pair['name']}_problem.denote := rfl")
        w("")
        w(f'def {pair["name"]}_entry : Entry := ⟨"{pair["name"]}", "agrees", {pair["name"]}, .{pair["status"]}⟩')
        w("")
    w("end Pairs")
    w("")
    w("/-- Every probe's harness. -/")
    w("def harnesses : List Harness :=")
    w("  [" + ",\n   ".join(f"{p['data']}.harness" for p in cat["probes"]) + "]")
    w("")
    w("/-- Every statement of the corpus, with its status. -/")
    w("def entries : List Entry :=")
    items = [f"{d}.{s['name']}_entry" for d, s in entries] + [f"Pairs.{p['name']}_entry" for p in cat["pairs"]]
    w("  [" + ",\n   ".join(items) + "]")
    w("")
    w(f"end {NS}.Corpus")
    return "\n".join(out) + "\n"


def settled_keys(cat: dict) -> list[str]:
    keys = []
    for probe in cat["probes"]:
        for s in probe["statements"]:
            if s["status"] != "stated":
                keys.append(f"{probe['probe']}/{s['name']}")
    for pair in cat["pairs"]:
        if pair["status"] != "stated":
            keys.append(f"{pair['name']}/agrees")
    return keys


def results_keys(text: str, cat: dict) -> list[str]:
    """The entries `Results.results` lists, by their generated names."""
    data = {p["data"]: p["probe"] for p in cat["probes"]}
    block = text.split("def results : List Settled :=", 1)
    if len(block) < 2:
        return []
    keys = []
    for match in re.finditer(r"Corpus\.(\w+)\.(\w+)_entry", block[1]):
        ns, name = match.groups()
        keys.append(f"{name}/agrees" if ns == "Pairs" else f"{data.get(ns, ns)}/{name}")
    return keys


def check(root: Path) -> list[str]:
    cat = load(root)
    problems = validate(root, cat)
    if problems:
        return problems
    corpus = root / CORPUS
    if not corpus.exists() or corpus.read_text() != gen(cat):
        problems.append(f"{CORPUS} is stale; run gen")
    results = root / RESULTS
    if results.exists():
        listed = results_keys(results.read_text(), cat)
        expected = settled_keys(cat)
        if sorted(listed) != sorted(expected):
            missing = sorted(set(expected) - set(listed))
            extra = sorted(set(listed) - set(expected))
            problems.append(f"{RESULTS}: results differ from the catalogue (missing {missing}, extra {extra})")
        text = results.read_text()
        if "sorry" in text or re.search(r"^\s*axiom\b", text, re.MULTILINE) or "native_decide" in text:
            problems.append(f"{RESULTS} uses sorry, axiom or native_decide")
    else:
        problems.append(f"{RESULTS} is missing")
    return problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=ROOT)
    sub = parser.add_subparsers(dest="command")
    sub.add_parser("gen")
    sub.add_parser("check")
    sub.add_parser("summary")
    args = parser.parse_args(argv)
    root = args.root
    cat = load(root)
    if args.command == "gen":
        problems = validate(root, cat)
        if problems:
            print("\n".join(problems), file=sys.stderr)
            return 1
        (root / CORPUS).write_text(gen(cat))
        print(f"wrote {CORPUS}")
        return 0
    if args.command == "summary":
        counts: dict[str, int] = {}
        everything = [s for probe in cat["probes"] for s in probe["statements"]] + cat["pairs"]
        for s in everything:
            counts[s["status"]] = counts.get(s["status"], 0) + 1
            if s["status"] == "refuted":
                key = f"refuted:{s['refutedBy']}"
                counts[key] = counts.get(key, 0) + 1
        print(json.dumps(counts, sort_keys=True))
        return 0
    problems = check(root)
    if problems:
        print("x86 probe problems: FAILED")
        for problem in problems:
            print(f"  {problem}")
        return 1
    print("x86 probe problems: catalogue, Corpus.lean and Results.lean agree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
