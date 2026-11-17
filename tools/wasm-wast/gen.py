#!/usr/bin/env python3
"""Turn a slice of the pinned WebAssembly spec test suite into kernel-checked problem rows.

    python3 -I tools/wasm-wast/gen.py convert   # pinned wasm-tools json-from-wast on FILES
    python3 -I tools/wasm-wast/gen.py probe     # classify every command (one native Lean run)
    python3 -I tools/wasm-wast/gen.py emit      # write the Lean modules and the report
    python3 -I tools/wasm-wast/gen.py fetch-wasmtime  # download the pinned wasmtime, SHA-256 checked
    python3 -I tools/wasm-wast/gen.py oracle    # run the pinned wasmtime on every command
    python3 -I tools/wasm-wast/gen.py oracle --check  # re-run wasmtime; fail on any difference (CI)
    python3 -I tools/wasm-wast/gen.py verify    # re-check oracle.json's provenance (no wasmtime)
    python3 -I tools/wasm-wast/gen.py regress   # wasmtime must reject deliberately wrong expectations (CI)
    python3 -I tools/wasm-wast/gen.py all       # convert, probe, emit, oracle, in order
    python3 -I tools/wasm-wast/gen.py site DIR  # copy report.json, oracle.json to DIR/wast/ (explorer)

Inputs are pinned: the spec test suite and wasm-tools by tools/wasm-tools/tests/pins.sh
(installed by tools/wasm-tools/tests/fetch-pins.sh spec wasm-tools), wasmtime 50.0.0 by
tools/wasm-jco/tests/pins.sh. Each is checked against its SHA-256 before use. Downloads and
generated JSON are data: this script parses them and never executes anything inside them.

`assert_invalid` and binary `assert_malformed` commands are answered by the tool-level shapes
`silmaril.shapes.wasm.wast.validator_rejects` / `decoder_rejects` (`decide +kernel` on
`validatorRejectsB` / `decode?`): claims about silmaril-lean's decoder and validator, not about
the specification. Text `assert_malformed` commands stay unsupported (TEXT_MALFORMED).

The files in SPEC (f32, f64, f32_bitwise, f64_bitwise, float_misc, conversions) are checked under
the specification profile `Profile.spec` by `scriptSK` (`ScriptHoldsS.of_kernel`): their WAST
patterns `nan:canonical`/`nan:arithmetic` are allowed sets, and each command gives a
`returns_allowed_all`/`traps_all` row (every normal form) and a `terminates_all` row (every run).
For them the probe computes the class of the specification's result set instead of running the
interpreter.

The files in LINK_FILES (imports, linking, exports, start, global, data, elem) are linked
scripts: each file is one script, checked by one `decide +kernel` evaluation of `scriptLK`
(`Silmaril.Project.Shapes.WasmWastLink`) from the context `Init`, in which `spectest` is the closed
Wasm module `Spectest.module` (not a host; its print functions have empty bodies). Their rows are
`link.returns_only`/`link.traps_only`/`link.unlinkable`/`link.uninstantiable` after every earlier
module, `register` and action of the file; `register` and bare actions are `context` rows. The
oracle runs each linked file's script once (wasmtime with its own spectest); a command passes when
wasmtime gets past its line.

The probe runs silmaril-lean's interpreter natively (`lake env lean` on a generated file) only to
decide which commands to give to the kernel; nothing it prints is a proof. The proofs are the
`decide +kernel` evaluations of `scriptK` (or, for modules with data segments, of `scriptKM`, which
instantiates and runs on `KMem` stores) in the emitted modules (docs/projects/wasm-wast.md).

The oracle is test-wise agreement with an independent implementation, not a proof. `oracle`
records its provenance in oracle.json (wasmtime version, archive and binary SHA-256, the
SHA-256 of report.json, of the spec files and of every generated script, and a UTC timestamp).
`verify` re-checks that record against the current pins and report.json without running
wasmtime, and, when the converted JSON of `convert` is present, regenerates every script and
compares its SHA-256.
"""
import datetime
import hashlib
import json
import os
import pathlib
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parents[2]
WORK = pathlib.Path(os.environ.get("WASM_WAST_WORK", pathlib.Path.home() / ".cache/silmaril-tools/wasm-wast"))
LEAN_DIR = ROOT / "Silmaril/Project/WasmWast"
REPORT = ROOT / "examples/wasm-wast/report.json"
ORACLE = ROOT / "examples/wasm-wast/oracle.json"
# The slice: spec test files, with their Lean module names.
FILES = [("i32", "I32"), ("i64", "I64"), ("int_exprs", "IntExprs"), ("fac", "Fac"), ("traps", "Traps"), ("address", "Address"),
         ("f32", "F32"), ("f64", "F64"), ("f32_bitwise", "F32Bitwise"), ("f64_bitwise", "F64Bitwise"),
         ("float_misc", "FloatMisc"), ("conversions", "Conversions")]
# Files whose assert_return/assert_trap commands are checked under the specification profile
# `Profile.spec` (nondeterministic NaN payloads), by `scriptSK` (`ScriptHoldsS.of_kernel`): every
# exported function must be straight-line numeric (`StraightLine.fn?`), and each command's claims
# are `returns_allowed_all`/`traps_all` (every normal form) and `terminates_all` (every run), with
# the WAST patterns `nan:canonical`/`nan:arithmetic` as allowed sets. The other files keep the
# deterministic profile (`returns_only`/`traps_only`).
SPEC = {"f32", "f64", "f32_bitwise", "f64_bitwise", "float_misc", "conversions"}
SPEC_SHAPE = {"assert_return": "silmaril.shapes.wasm.wast.returns_allowed_all",
              "assert_trap": "silmaril.shapes.wasm.wast.traps_all"}
TERM_SHAPE = "silmaril.shapes.wasm.wast.terminates_all"
PROFILE_SPEC = "Profile.spec (nan := .spec: float operators return the specification's result sets; $ND = true, default relaxed choices; the kernel theorems hold for every $ND and relaxed choice)"
PROFILE_DET = "profile neverFail (deterministic: canonical NaNs, $ND = false, grow fails only when impossible)"
FUEL = 100000
# Modules with data segments are checked on KMem stores (`scriptKM`, `ScriptHolds.of_kernelKM`):
# the kernel evaluates `ByteArray` writes (`ByteArray.copySlice`) element by element over the whole
# 64 KiB page and exceeds its recursion limit, while `KMem` writes touch only the leaves they need.
# The claims are the same (`scriptK_of_scriptKM`). Modules without data segments keep `scriptK`.
# KERNEL_OUT lists modules ("file/index") whose kernel evaluation is still out of reach, with the
# reason; their commands are undetermined. It is empty.
KERNEL_OUT = {}
O = "Silmaril.Wasm.SingleThreaded.neverFail"
# Text-format `assert_malformed` (`module quote` that wasm-tools cannot encode): no binary exists.
# silmaril-lean's WAT front end `Tools.Parse.textModule` rejects all four of the slice natively,
# with its `.syntax` error, but that error also covers text outside its elaborator and the front
# end has no completeness theorem: a kernel row would not separate malformed from unsupported text.
TEXT_MALFORMED = ("assert_malformed on text: no binary; silmaril-lean's WAT front end has no completeness "
                  "theorem and its syntax error also covers unsupported text (no shape)")
# The rejection shapes: (shape, Lean name, kernel checker) by the function that rejects.
REJECT = {"validator": ("silmaril.shapes.wasm.wast.validator_rejects", "ValidatorRejects", "validatorRejectsB"),
          "decoder": ("silmaril.shapes.wasm.wast.decoder_rejects", "DecoderRejects", "decode?")}
# Which rejection each assertion expects (another one is a mismatch).
REJECT_WANT = {"assert_invalid": "validator", "assert_malformed": "decoder"}
# Linked scripts: whole files with several modules, imports, `register`, named modules, `get` and
# the `spectest` module, checked by `scriptLK` (`Silmaril.Project.Shapes.WasmWastLink`): one kernel
# evaluation per file runs the whole script in order, from the context `Init` (the closed module
# `Spectest.module` registered as "spectest"), on KMem stores.
# names.wast is left out for kernel time: its third module (7.6 KB, 480 exports) exceeds 33 GB of
# memory within two minutes of the kernel check (the native probe passes all 482 assert_return).
LINK_FILES = [("imports", "Imports"), ("linking", "Linking"), ("exports", "Exports"), ("start", "Start"),
              ("global", "Global"), ("data", "Data"), ("elem", "Elem")]
LINK = {f for f, _ in LINK_FILES}
LINK_SHAPE = {"assert_return": "silmaril.shapes.wasm.wast.link.returns_only",
              "assert_trap": "silmaril.shapes.wasm.wast.link.traps_only",
              "assert_unlinkable": "silmaril.shapes.wasm.wast.link.unlinkable",
              "assert_uninstantiable": "silmaril.shapes.wasm.wast.link.uninstantiable"}
LINK_STRENGTH = {"assert_return": "only", "assert_trap": "only", "assert_unlinkable": "link",
                 "assert_uninstantiable": "only"}
HOST_MODEL = ("spectest = the closed Wasm module Spectest.module (Silmaril.Project.Shapes.WasmWastLink.Defs), "
              "allocated once per script and registered as \"spectest\": globals 666/666/666.6/666.6, table and table64 "
              "10..20 funcref, memory 1..2; its print functions have empty bodies (no values, store unchanged: "
              "Spectest.print_nf); printed output is erased and not claimed; no .host function instance; "
              "the oracle uses wasmtime's own spectest")
REGRESS = ROOT / "tools/wasm-wast/regress"
NS = "silmaril.wasm_wast"


def pins(path):
    """The NAME=value assignments of a pins.sh (only literal values and $VAR references)."""
    env = {"HOME": str(pathlib.Path.home())}
    for line in (ROOT / path).read_text().splitlines():
        m = re.match(r"^([A-Z0-9_]+)=(\S+)$", line)
        if not m:
            continue
        v = m.group(2)
        v = re.sub(r"\$\{([A-Z0-9_]+):-([^}]*)\}", lambda x: os.environ.get(x.group(1), env.get(x.group(1), x.group(2))), v)
        v = re.sub(r"\$([A-Z0-9_]+)", lambda x: env.get(x.group(1), ""), v)
        env[m.group(1)] = v
    return env


def sha256(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def need(p, sha, what):
    if not pathlib.Path(p).is_file():
        sys.exit(f"gen.py: {what} not installed at {p}")
    if sha256(p) != sha:
        sys.exit(f"gen.py: {what} at {p} does not match its pinned SHA-256 {sha}")


WT = pins("tools/wasm-tools/tests/pins.sh")
JCO = pins("tools/wasm-jco/tests/pins.sh")
SPEC_CORE = pathlib.Path(WT["WASM_SPEC_DIR"]) / f"spec-{WT['WASM_SPEC_REV']}" / "test/core"


def convert():
    need(WT["WT_UPSTREAM"], WT["WT_UPSTREAM_SHA256"], "wasm-tools")
    need(WT["WASM_SPEC_ARCHIVE"], WT["WASM_SPEC_SHA256"], "the spec test suite archive")
    recorded = {x["file"]: x["sha256"] for x in json.loads(REPORT.read_text())["files"]} if REPORT.is_file() else {}
    for f, _ in FILES + LINK_FILES:
        d = WORK / "json" / f
        d.mkdir(parents=True, exist_ok=True)
        # The unpacked spec file must be the one report.json records (fetch-pins.sh checks only the
        # archive, and an unpacked tree may be cached).
        want = recorded.get(f"test/core/{f}.wast")
        if want is not None and sha256(SPEC_CORE / f"{f}.wast") != want:
            sys.exit(f"gen.py: {SPEC_CORE / f'{f}.wast'} does not match the SHA-256 {want} recorded in report.json")
        subprocess.run([WT["WT_UPSTREAM"], "json-from-wast", str(SPEC_CORE / f"{f}.wast"), "-o", str(d / f"{f}.json"),
                        "--wasm-dir", str(d)], check=True)
        print(f"convert {f}: {d / (f + '.json')}")


# ---------- values ----------

WIDTH = {"i32": 32, "i64": 64, "f32": 32, "f64": 64}


def lean_val(v):
    t, x = v["type"], v.get("value")
    if t not in WIDTH or x is None or not re.fullmatch(r"-?[0-9]+", str(x)):
        return None
    n = int(x) % (1 << WIDTH[t])
    return f"Val.{t} {n}" if t in ("i32", "i64") else f"Val.num ⟨.float .{t}, {n}⟩"


def lean_pat(v):
    """The `ValPat` of an expected result: `nan:canonical`/`nan:arithmetic` patterns, or the exact
    value (compared as bits)."""
    t, x = v["type"], v.get("value")
    if t in ("f32", "f64") and x in ("nan:canonical", "nan:arithmetic"):
        return f".{'canonicalNaN' if x == 'nan:canonical' else 'arithmeticNaN'} .{t}"
    lv = lean_val(v)
    return None if lv is None else f".exact ({lv})"


def show_val(v):
    """`type:bits` with the bits as an unsigned decimal (as the interpreter's observation is
    printed), or the WAST text of a pattern such as `nan:canonical`."""
    t, x = v["type"], v.get("value")
    if t in WIDTH and re.fullmatch(r"-?[0-9]+", str(x)):
        return f"{t}:{int(x) % (1 << WIDTH[t])}"
    return f"{t}:{x}"


def lean_str(s):
    """A Lean string literal: printable characters as they are, the others as `\\xHH` / `\\uHHHH`
    escapes (Lean has no `\\b` or `\\f`)."""
    out = []
    for ch in s:
        o = ord(ch)
        if ch in ('"', "\\"):
            out.append("\\" + ch)
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\t":
            out.append("\\t")
        elif o < 0x20 or o == 0x7F:
            out.append(f"\\x{o:02x}")
        elif 0x80 <= o < 0xA0 or 0xD800 <= o <= 0xDFFF:
            out.append(f"\\u{o:04x}")
        else:
            out.append(ch)
    return '"' + "".join(out) + '"'


def wast_str(s):
    """A WAST string literal: printable ASCII as it is, every other character as a `\\u{H}`
    escape (the same text as `json.dumps` on printable ASCII)."""
    out = []
    for ch in s:
        o = ord(ch)
        if ch in ('"', "\\"):
            out.append("\\" + ch)
        elif o < 0x20 or o >= 0x7F:
            # wasmtime's lexer rejects unescaped "confusing" characters (bidi controls, zero
            # widths); every non-ASCII character is escaped, so the text is ASCII.
            out.append(f"\\u{{{o:x}}}")
        else:
            out.append(ch)
    return '"' + "".join(out) + '"'


# ---------- the script model: segments of a module and its commands ----------

def load(f):
    d = json.loads((WORK / "json" / f / f"{f}.json").read_text())
    segs, cur, rows = [], None, []
    for c in d["commands"]:
        row = {"id": f"{f}:{c['line']}", "file": f, "line": c["line"], "type": c["type"]}
        t = c["type"]
        if t == "module":
            cur = {"file": f, "index": len(segs), "line": c["line"], "wasm": c.get("filename"), "named": c.get("name"),
                   "module_type": c.get("module_type"), "cmds": []}
            segs.append(cur)
            row["status"] = "module"
            rows.append(row)
            continue
        act = c.get("action")
        if act:
            row["action"] = {"field": act.get("field"), "args": act.get("args", []), "module": act.get("module"),
                             "type": act.get("type")}
        if "expected" in c:
            row["expected"] = c["expected"]
        if "text" in c:
            row["text"] = c["text"]
        rows.append(row)
        reason = None
        if t in ("assert_invalid", "assert_malformed"):
            # The binary of the module: given (`module binary`), or written by wasm-tools for a
            # text module it can encode (`binary_filename`, e.g. `assert_invalid` on text).
            fn = c.get("binary_filename") or (c.get("filename") if c.get("module_type") == "binary" else None)
            row["module_type"] = c.get("module_type")
            if fn:
                row["status"], row["reject_wasm"] = "reject_candidate", fn
            else:
                row["status"], row["reason"] = "unsupported", TEXT_MALFORMED
            continue
        if t in ("assert_unlinkable", "assert_uninstantiable", "register",
                 "module_definition", "module_instance", "assert_exception", "assert_suspension"):
            reason = {"assert_unlinkable": "assert_unlinkable (no shape)",
                      "assert_uninstantiable": "assert_uninstantiable (no shape)"}.get(t, f"{t} (no shape)")
            row["status"], row["reason"] = "unsupported", reason
            continue
        if cur is None:
            row["status"], row["reason"] = "unsupported", "no current module"
            continue
        row["seg"] = cur["index"]
        if t == "assert_exhaustion":
            row["status"], row["reason"] = "unsupported", "assert_exhaustion: resource exhaustion is not modelled"
            row["truncates"] = True
        elif act is None or act.get("type") != "invoke":
            row["status"], row["reason"] = "unsupported", f"action {act and act.get('type')} (only invoke)"
            row["truncates"] = True
        elif act.get("module"):
            row["status"], row["reason"] = "unsupported", "action on a named module"
        else:
            args = [lean_val(v) for v in act.get("args", [])]
            if None in args:
                row["status"], row["reason"] = "unsupported", "argument type outside i32/i64/f32/f64"
                row["truncates"] = True
            else:
                row["lean_args"] = args
                if t == "action":
                    row["expect"] = None
                    row["status"] = "action"
                elif t == "assert_return" and f in SPEC:
                    pats = [lean_pat(v) for v in c.get("expected", [])]
                    if None in pats:
                        row["status"], row["reason"], row["expect"] = "unsupported", "result type outside i32/i64/f32/f64", None
                    else:
                        row["expect"] = ("values", pats)
                        row["status"] = "candidate"
                elif t == "assert_return":
                    exp = [lean_val(v) for v in c.get("expected", [])]
                    if None in exp:
                        pats = [str(v.get("value")) for v in c.get("expected", []) if lean_val(v) is None]
                        kind = "NaN pattern (allowed-set shape not implemented)" if any("nan:" in p for p in pats) \
                            else "result type outside i32/i64/f32/f64"
                        row["status"], row["reason"], row["expect"] = "unsupported", kind, None
                    else:
                        row["expect"] = ("values", exp)
                        row["status"] = "candidate"
                elif t == "assert_trap":
                    row["expect"] = ("trap", None)
                    row["status"] = "candidate"
                else:
                    row["status"], row["reason"], row["expect"] = "unsupported", f"{t} (no shape)", None
        if "lean_args" in row:
            cur["cmds"].append(row)
        elif row.get("truncates"):
            cur["cmds"].append(row)
    return segs, rows


def seg_reason(seg):
    if seg["named"]:
        return None  # named modules are fine as the current module; actions naming them are skipped
    if seg["module_type"] != "binary":
        return f"module given as {seg['module_type']}"
    return None


def lean_cmd(row, with_expect=True):
    args = ", ".join(row["lean_args"])
    e = row.get("expect")
    if not with_expect or e is None:
        es = "none"
    elif e[0] == "values":
        es = f"some (.values [{', '.join(e[1])}])"
    else:
        es = "some .trap"
    return f"⟨⟨{lean_str(row['action']['field'])}, [{args}]⟩, {es}⟩"


def bytes_lean(name, data):
    out, line = [], []
    for i, b in enumerate(data):
        line.append(str(b))
        if len(line) == 24:
            out.append(", ".join(line))
            line = []
    if line:
        out.append(", ".join(line))
    return f"def {name} : ByteArray := ⟨#[\n  " + ",\n  ".join(out) + "]⟩\n"


def runnable(seg):
    """The commands that can be given to the interpreter: up to the first truncating one."""
    out = []
    for r in seg["cmds"]:
        if r.get("truncates"):
            break
        out.append(r)
    return out


# ---------- linked scripts: whole files with imports, register and the closed spectest module ----------

LINK_PROBE = r"""
section LinkProbe
open Silmaril.Project.Shapes.WasmWastLink hiding Ctx Action Cmd NF pre Only Reaches ReturnsOnly TrapsOnly ScriptHolds ScriptAt Run Always

abbrev LCtx := Silmaril.Project.Shapes.WasmWastLink.Ctx
abbrev LAction := Silmaril.Project.Shapes.WasmWastLink.Action
abbrev LCmd := Silmaril.Project.Shapes.WasmWastLink.Cmd

def runP (fuel : Nat) (c : Config Nat) : Option (Config Nat) :=
  let r := Exec.runI neverFail fuel c
  if r.2 then some r.1 else none

def instP (fuel : Nat) (ctx : LCtx) (m : Module) : Except String (Config Nat × ModuleInst) :=
  match validate? m with
  | none => .error "the validator rejects the module"
  | some mt =>
    match resolve? ctx.regs m.imports with
    | none => .error "an import does not resolve to an export of a registered module"
    | some xas =>
      if externAddrsOk? ctx.store xas mt.imports then
        match instantiateOnce? ctx.store m xas with
        | some (s, f, st) =>
          match runP fuel ⟨s, f, startCode st⟩ with
          | some c => .ok (c, f.module)
          | none => .error s!"the start function did not stop ({fuel} steps)"
        | none => .error "instantiateOnce? fails (a segment initialisation is out of bounds, or allocation fails)"
      else .error "the import types do not match"

def showOut : Option Result → String
  | some r => showRes r
  | none => "a normal form that is not a result (stuck)"

def actP (fuel : Nat) (ctx : LCtx) : LAction → Except (String × String) (Result × Store Nat)
  | .invoke t name args =>
    match ctx.inst? t with
    | some mi =>
      match exportFunc? mi name with
      | some a =>
        if invokeOkB ctx.store a args then
          match runP fuel (invoke ctx.store a args) with
          | some c =>
            match c.outcome? with
            | some r => .ok (r, c.store)
            | none => .error ("error", "stopped without a result (stuck)")
          | none => .error ("undetermined", s!"out of fuel ({fuel} steps)")
        else .error ("error", "arguments not typed")
      | none => .error ("error", "no function export")
    | none => .error ("error", "no such module")
  | .get t name =>
    match ctx.inst? t with
    | some mi =>
      match exportAddr? mi name with
      | some (.global a) =>
        match ctx.store.globals[a]? with
        | some gi => .ok (.values [gi.value], ctx.store)
        | none => .error ("error", "no global")
      | _ => .error ("error", "no global export")
    | none => .error ("error", "no such module")

partial def probeL (tag : String) (fuel : Nat) : Nat → LCtx → List LCmd → IO Unit
  | _, _, [] => pure ()
  | k, ctx, .module name m :: cmds =>
    match instP fuel ctx m with
    | .ok (c, mi) =>
      if decide (c.outcome? = some (.values [])) then do
        IO.println s!"P\t{tag}\t{k}\tran\tinstantiated"
        probeL tag fuel (k + 1)
          { ctx with store := c.store, cur := some mi, named := bindName name mi ctx.named } cmds
      else IO.println s!"P\t{tag}\t{k}\terror\tmodule: the start code ends with {showOut c.outcome?}"
    | .error e => IO.println s!"P\t{tag}\t{k}\terror\tmodule: {e}"
  | k, ctx, .register as t :: cmds =>
    match ctx.inst? t with
    | some mi => do
      IO.println s!"P\t{tag}\t{k}\tran\tregistered"
      probeL tag fuel (k + 1) { ctx with regs := (as, mi) :: ctx.regs } cmds
    | none => IO.println s!"P\t{tag}\t{k}\terror\tregister: no such module"
  | k, ctx, .action act e :: cmds =>
    match actP fuel ctx act with
    | .ok (r, s) => do
      let ok := match e with
        | some e => if decide (r = e.result) then "pass" else "mismatch"
        | none => "ran"
      IO.println s!"P\t{tag}\t{k}\t{ok}\t{showRes r}"
      probeL tag fuel (k + 1) { ctx with store := s } cmds
    | .error (st, d) => IO.println s!"P\t{tag}\t{k}\t{st}\t{d}"
  | k, ctx, .unlinkable m _ :: cmds => do
    if (validate? m).isNone then IO.println s!"P\t{tag}\t{k}\terror\tthe validator rejects the module" else
    if unlinkableG ctx m then do
      let why := match resolve? ctx.regs m.imports with
        | none => "an import does not resolve"
        | some _ => "the import types do not match"
      IO.println s!"P\t{tag}\t{k}\tpass\tunlinkable: {why}"
      probeL tag fuel (k + 1) ctx cmds
    else IO.println s!"P\t{tag}\t{k}\tmismatch\tthe module links"
  | k, ctx, .uninstantiable m _ :: cmds =>
    match instP fuel ctx m with
    | .ok (c, _) =>
      match c.outcome? with
      | some .trap => do
        IO.println s!"P\t{tag}\t{k}\tpass\tthe start function traps"
        probeL tag fuel (k + 1) { ctx with store := c.store } cmds
      | some r => do
        IO.println s!"P\t{tag}\t{k}\tmismatch\tthe start code ends with {showRes r}"
        probeL tag fuel (k + 1) { ctx with store := c.store } cmds
      | none => IO.println s!"P\t{tag}\t{k}\terror\tthe start code ends with {showOut none}"
    | .error e => IO.println s!"P\t{tag}\t{k}\terror\tinstantiation: {e}"

def probeLink (tag : String) (fuel : Nat) (cmds : List LCmd) : IO Unit :=
  match validate? Spectest.module, instantiateOnce? (Game.importStore []) Spectest.module [] with
  | some _, some (s, f, none) => probeL tag fuel 0 { store := s, regs := [("spectest", f.module)] } cmds
  | _, _ => IO.println s!"P\t{tag}\t0\terror\tspectest does not instantiate"

end LinkProbe
"""


def lean_res(v):
    """An expected result as a Lean value: exact numbers, or a null reference (`ref.null`, an
    untyped `Ref.null` in Core); `None` for patterns (NaN classes, non-null references)."""
    if v["type"] in ("externref", "funcref", "anyref", "exnref") and v.get("value") == "null" or v["type"] == "refnull":
        return "Val.ref .null"
    return lean_val(v)


def show_res(v):
    if v["type"] == "refnull" or v.get("value") == "null":
        return f"{v['type']}:null"
    if v.get("value") is None:
        return f"{v['type']}:(ref.func)" if v["type"] == "funcref" else f"{v['type']}:?"
    return show_val(v)


def load_link(f):
    """The script of a linked file: the commands in order (`items`, the Cmd candidates), and one
    report row per command that is not a module."""
    d = json.loads((WORK / "json" / f / f"{f}.json").read_text())
    items, rows, nmod = [], [], 0
    for c in d["commands"]:
        t, line = c["type"], c["line"]
        if t == "module":
            it = {"kind": "module", "line": line, "name": c.get("name"), "wasm": c.get("filename"), "index": nmod}
            nmod += 1
            if c.get("module_type") != "binary":
                it["stop"] = f"module given as {c.get('module_type')}"
            items.append(it)
            continue
        row = {"id": f"{f}:{line}", "file": f, "line": line, "type": t, "link": True}
        rows.append(row)
        if "text" in c:
            row["text"] = c["text"]
        if t in ("assert_invalid", "assert_malformed"):
            fn = c.get("binary_filename") or (c.get("filename") if c.get("module_type") == "binary" else None)
            row["module_type"] = c.get("module_type")
            if fn:
                row["status"], row["reject_wasm"] = "reject_candidate", fn
            else:
                row["status"], row["reason"] = "unsupported", TEXT_MALFORMED
            continue
        if t == "register":
            row["register"] = {"as": c["as"], "module": c.get("name")}
            items.append({"kind": "register", "row": row, "as": c["as"], "target": c.get("name")})
            continue
        if t in ("assert_unlinkable", "assert_uninstantiable"):
            row["module_type"] = c.get("module_type")
            if c.get("module_type") != "binary":
                row["status"], row["reason"] = "unsupported", f"module given as {c.get('module_type')}"
                items.append({"kind": "stop", "row": row})
                continue
            row["link_wasm"] = c["filename"]
            items.append({"kind": t.removeprefix("assert_"), "row": row, "wasm": c["filename"]})
            continue
        act = c.get("action")
        if t in ("action", "assert_return", "assert_trap") and act:
            row["action"] = {"field": act.get("field"), "args": act.get("args", []), "module": act.get("module"),
                             "type": act.get("type")}
            if "expected" in c:
                row["expected"] = c["expected"]
            args = [lean_val(v) for v in act.get("args", [])]
            if act.get("type") not in ("invoke", "get"):
                row["status"], row["reason"] = "unsupported", f"action {act.get('type')}"
                items.append({"kind": "stop", "row": row})
                continue
            if None in args:
                row["status"], row["reason"] = "unsupported", "argument type outside i32/i64/f32/f64 (the action cannot be run)"
                items.append({"kind": "stop", "row": row})
                continue
            row["lean_args"] = args
            expect = None
            if t == "assert_return":
                exp = [lean_res(v) for v in c.get("expected", [])]
                if None in exp:
                    pats = [str(v.get("value")) for v in c.get("expected", []) if lean_res(v) is None]
                    row["status"] = "unsupported"
                    row["reason"] = ("NaN pattern (allowed-set shape not implemented for linked scripts)" if any("nan:" in p for p in pats)
                                     else "result pattern outside exact numbers and null references")
                else:
                    expect = ("values", exp)
            elif t == "assert_trap":
                expect = ("trap", None)
            items.append({"kind": "act", "row": row, "expect": expect})
            continue
        row["status"], row["reason"] = "unsupported", f"{t} (no shape)"
        items.append({"kind": "stop", "row": row})
    return items, rows


def link_runnable(items):
    out = []
    for it in items:
        if it["kind"] == "stop" or it.get("stop"):
            break
        out.append(it)
    return out


def lean_target(name):
    return ".cur" if not name else f"(.named {lean_str(name)})"


def lean_link_action(row):
    a = row["action"]
    if a["type"] == "get":
        return f".get {lean_target(a['module'])} {lean_str(a['field'])}"
    return f".invoke {lean_target(a['module'])} {lean_str(a['field'])} [{', '.join(row['lean_args'])}]"


def link_mod_var(it):
    return f"m{it['index']}" if it["kind"] == "module" else f"u{it['row']['line']}"


def lean_link_cmd(it, claim):
    k = it["kind"]
    if k == "module":
        return f".module {'none' if not it['name'] else '(some ' + lean_str(it['name']) + ')'} {link_mod_var(it)}"
    if k == "register":
        return f".register {lean_str(it['as'])} {lean_target(it['target'])}"
    if k in ("unlinkable", "uninstantiable"):
        return f".{k} {link_mod_var(it)} {'true' if claim else 'false'}"
    e = it["expect"] if claim else None
    es = "none" if e is None else (f"(some (.values [{', '.join(e[1])}]))" if e[0] == "values" else "(some .trap)")
    return f".action ({lean_link_action(it['row'])}) {es}"


def link_wasm(f, it):
    return (WORK / "json" / f / (it["wasm"])).read_bytes()


def probe_link(out):
    for f, _ in LINK_FILES:
        items, rows = load_link(f)
        run = link_runnable(items)
        for it in run:
            if it["kind"] in ("module", "unlinkable", "uninstantiable"):
                out.append(bytes_lean(f"b_{f}_{link_mod_var(it)}", link_wasm(f, it)))
        defs = "".join(f"def mod_{f}_{link_mod_var(it)} : Module := (Silmaril.Wasm.Binary.Core.decode? b_{f}_{link_mod_var(it)}).getD {{}}\n"
                       for it in run if it["kind"] in ("module", "unlinkable", "uninstantiable"))
        out.append(defs)
        for it in run:
            if it["kind"] in ("module", "unlinkable", "uninstantiable"):
                out.append(f"#eval if (Silmaril.Wasm.Binary.Core.decode? b_{f}_{link_mod_var(it)}).isNone then "
                           f"IO.println \"D\\t{f}\\t{link_mod_var(it)}\" else pure ()\n")
        for k, it in enumerate(run):
            if it["kind"] in MODKINDS:
                out.append(f"#eval IO.println (\"I\\tlink:{f}/{k}\\t\" ++ \",\".intercalate "
                           f"(mod_{f}_{link_mod_var(it)}.imports.map fun i => i.moduleName ++ \".\" ++ i.name))\n")
        cmds = [lean_link_cmd(it, True).replace(f" {link_mod_var(it)}", f" mod_{f}_{link_mod_var(it)}")
                if it["kind"] in ("module", "unlinkable", "uninstantiable") else lean_link_cmd(it, True) for it in run]
        out.append(f"set_option maxRecDepth 100000 in\n#eval probeLink {lean_str('link:' + f)} {FUEL} [\n  " + ",\n  ".join(cmds) + "]\n")
        for r in rows:
            if r.get("status") == "reject_candidate":
                out.append(bytes_lean(f"r_{f}_{r['line']}", (WORK / "json" / f / r["reject_wasm"]).read_bytes()))
                out.append(f"#eval probeReject {lean_str(r['id'])} r_{f}_{r['line']}\n")


MODKINDS = ("module", "unlinkable", "uninstantiable")


def classify_link(pr):
    """Statuses of the rows of the linked files, the commands the kernel runs (with their claims),
    and the script context of each row (registered names, named modules, the current module and
    its imports, the host model)."""
    files = []
    for f, mod in LINK_FILES:
        items, rows = load_link(f)
        run = link_runnable(items)
        undec = set(pr.get("link_decode", {}).get(f, []))
        imps = pr.get("link_imports", {})
        kernel, end, why = [], len(run), None
        regs, named, cur, cur_imports = ["spectest"], [], None, []
        for k, it in enumerate(run):
            row = it.get("row")
            p = pr["cmds"].get(f"link:{f}/{k}")
            if it["kind"] in MODKINDS and link_mod_var(it) in undec:
                p = {"status": "unsupported", "detail": "silmaril-lean's decoder rejects the module"}
            if p is None or p["status"] in ("error", "undetermined", "unsupported"):
                st = "undetermined" if p and p["status"] == "undetermined" else "unsupported"
                why = p["detail"] if p else "not probed"
                if row is not None:
                    row["status"], row["reason"] = st, why
                else:
                    why = f"the module at line {it['line']} does not instantiate in silmaril-lean: {why}"
                end = k
                break
            ctx = {"registered": list(regs), "named": list(named), "current": cur,
                   "current_imports": list(cur_imports), "host": "spectest = closed Spectest.module"}
            if it["kind"] == "module":
                cur = f"${it['name']}" if it["name"] else f"module at line {it['line']}"
                cur_imports = imps.get(f"link:{f}/{k}", [])
                if it["name"]:
                    named.insert(0, it["name"])
                kernel.append((it, False))
                continue
            row["context"] = ctx
            if it["kind"] in ("unlinkable", "uninstantiable"):
                row["context"] = {**ctx, "module_imports": imps.get(f"link:{f}/{k}", [])}
            if it["kind"] == "register":
                regs.insert(0, it["as"])
                row["status"], row["reason"] = "context", "register: part of the script context of later rows (no claim)"
                kernel.append((it, False))
                continue
            row["observed"] = p["detail"]
            if p["status"] == "pass":
                row["status"] = "proved"
                kernel.append((it, True))
            elif p["status"] == "mismatch":
                row["status"], row["reason"] = "mismatch", "silmaril-lean's run differs from the expectation"
                kernel.append((it, False))
                if it["kind"] == "unlinkable":
                    # The reference interpreter would go on with a module that links: the context differs.
                    end, why = k + 1, "an earlier assert_unlinkable does not hold in silmaril-lean"
                    break
            else:
                if row.get("status") != "unsupported":
                    row["status"], row["reason"] = "context", "a bare action: part of the script context of later rows (no claim)"
                kernel.append((it, False))
        if why is None and end < len(items):
            stopper = items[end]
            why = stopper.get("stop") or (stopper.get("row") or {}).get("reason") or "an unsupported command"
            why = f"line {stopper.get('line') or stopper['row']['line']}: {why}"
        for i, it in enumerate(items):
            r = it.get("row")
            if r is None or i <= end and r.get("status") is not None:
                continue
            if r.get("status") == "unsupported":
                continue
            r["status"] = "undetermined"
            r["reason"] = f"an earlier command of the script did not run ({why})"
            r.pop("observed", None)
            r.pop("context", None)
        for r in rows:
            if r.get("status") is None:
                r["status"], r["reason"] = "undetermined", "not run"
            if r.get("status") == "reject_candidate":
                got = pr.get("rejects", {}).get(r["id"])
                want = REJECT_WANT[r["type"]]
                if got is not None:
                    r["observed"] = {"validator": "decode? reads a module; validate? rejects it",
                                     "decoder": "decode? rejects the bytes",
                                     "accepts": "decode? reads a module; validate? accepts it"}[got]
                if got == want:
                    r["status"], r["reject"] = "proved", got
                elif got is None:
                    r["status"], r["reason"] = "undetermined", "not probed"
                else:
                    r["status"] = "mismatch"
                    r["reason"] = f"{r['type']} expects a {want} rejection; silmaril-lean: {r['observed']}"
        files.append((f, mod, items, rows, kernel))
    return files


# ---------- probe ----------

PROBE_HEAD = """import Silmaril.Project.Shapes.WasmWast.Defs
import Silmaril.Project.Shapes.WasmWastLink.Defs
import Silmaril.Project.Shapes.WasmWastSpec.Defs
import Silmaril.Wasm.Binary.Core.Decode
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Project.Shapes.WasmWast
open Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
open Silmaril.Project.Shapes.WasmWastSpec (CmdS NumSet numericSet?)
set_option maxRecDepth 100000

def showVal : Val → String
  | .num ⟨.int .i32, b⟩ => s!"i32:{b.toNat}"
  | .num ⟨.int .i64, b⟩ => s!"i64:{b.toNat}"
  | .num ⟨.float .f32, b⟩ => s!"f32:{b.toNat}"
  | .num ⟨.float .f64, b⟩ => s!"f64:{b.toNat}"
  | .vec b => s!"v128:{b.toNat}"
  | .ref _ => "ref"

def showRes : Result → String
  | .values vs => "values " ++ " ".intercalate (vs.map showVal)
  | .trap => "trap"
  | .throw a => s!"throw {a}"

def probeCmds (tag : String) (fuel : Nat) (mi : ModuleInst) : Nat → Store Nat → List Cmd → IO Unit
  | _, _, [] => pure ()
  | k, s, cmd :: cmds => do
    match exportFunc? mi cmd.act.name with
    | none => IO.println s!"P\\t{tag}\\t{k}\\terror\\tno function export"
    | some a =>
      if !invokeOkB s a cmd.act.args then IO.println s!"P\\t{tag}\\t{k}\\terror\\targuments not typed" else
      match Exec.runInvoke? neverFail fuel s a cmd.act.args with
      | some (c, true, some r) =>
        let ok := match cmd.expect with
          | some e => if decide (c.outcome? = some e.result) then "pass" else "mismatch"
          | none => "ran"
        IO.println s!"P\\t{tag}\\t{k}\\t{ok}\\t{showRes r}"
        probeCmds tag fuel mi (k + 1) c.store cmds
      | some (_, false, _) => IO.println s!"P\\t{tag}\\t{k}\\tundetermined\\tout of fuel ({fuel} steps)"
      | _ => IO.println s!"P\\t{tag}\\t{k}\\terror\\tstopped without a result (stuck or host call)"

def probeReject (tag : String) (bytes : ByteArray) : IO Unit :=
  match Silmaril.Wasm.Binary.Core.decode? bytes with
  | none => IO.println s!"R\\t{tag}\\tdecoder"
  | some m =>
    match validate? m with
    | none => IO.println s!"R\\t{tag}\\tvalidator"
    | some _ => IO.println s!"R\\t{tag}\\taccepts"

def showFT : FloatType → String
  | .f32 => "f32"
  | .f64 => "f64"

def showSet : NumSet → String
  | .exact v => "values " ++ showVal v
  | .canonical t => s!"nan:canonical {showFT t}"
  | .arithmetic t => s!"nan:arithmetic {showFT t}"
  | .trap => "trap"

/-- The specification profile: no interpreter run, the class of the result set (the store does not
change: every function is straight-line numeric). -/
def probeSCmds (tag : String) (s : Store Nat) (mi : ModuleInst) : Nat → List CmdS → IO Unit
  | _, [] => pure ()
  | k, cmd :: cmds => do
    match exportFunc? mi cmd.act.name with
    | none => IO.println s!"P\\t{tag}\\t{k}\\terror\\tno function export"
    | some a =>
      match s.funcs[a]? with
      | none => IO.println s!"P\\t{tag}\\t{k}\\terror\\tno function"
      | some fi =>
        match StraightLine.fn? fi cmd.act.args.length with
        | none => IO.println s!"P\\t{tag}\\t{k}\\terror\\tnot a straight-line numeric function (local.get 0 ... local.get (k-1); op)"
        | some op =>
          match numericSet? op cmd.act.args with
          | none => IO.println s!"P\\t{tag}\\t{k}\\terror\\tno result class for the instruction and arguments"
          | some S =>
            let ok := match cmd.expect with
              | some e => if S.sub e then "pass" else "mismatch"
              | none => "ran"
            IO.println s!"P\\t{tag}\\t{k}\\t{ok}\\t{showSet S}"
            probeSCmds tag s mi (k + 1) cmds

def probeS (tag : String) (bytes : ByteArray) (cmds : List CmdS) : IO Unit := do
  match Silmaril.Wasm.Binary.Core.decode? bytes with
  | none => IO.println s!"M\\t{tag}\\tdecode\\tthe decoder rejects the module"
  | some m =>
    match validate? m with
    | none => IO.println s!"M\\t{tag}\\tvalidate\\tthe validator rejects the module"
    | some mt =>
      if !mt.imports.isEmpty then IO.println s!"M\\t{tag}\\timports\\tthe module has imports" else
      match instantiateOnce? (Game.importStore []) m [] with
      | some (s, f, none) => do
          IO.println s!"M\\t{tag}\\tok\\t{m.data.length}"
          probeSCmds tag s f.module 0 cmds
      | some (_, _, some _) => IO.println s!"M\\t{tag}\\tstart\\tthe module has a start function"
      | none => IO.println s!"M\\t{tag}\\tinstantiate\\tinstantiation fails (or traps)"

def probe (tag : String) (bytes : ByteArray) (cmds : List Cmd) : IO Unit := do
  match Silmaril.Wasm.Binary.Core.decode? bytes with
  | none => IO.println s!"M\\t{tag}\\tdecode\\tthe decoder rejects the module"
  | some m =>
    match validate? m with
    | none => IO.println s!"M\\t{tag}\\tvalidate\\tthe validator rejects the module"
    | some mt =>
      if !mt.imports.isEmpty then IO.println s!"M\\t{tag}\\timports\\tthe module has imports" else
      match instantiateOnce? (Game.importStore []) m [] with
      | some (s, f, none) =>
        if !exportsScalar s f.module then
          IO.println s!"M\\t{tag}\\texports\\ta function export has a non-scalar type"
        else do
          IO.println s!"M\\t{tag}\\tok\\t{m.data.length}"
          probeCmds tag {fuel} f.module 0 s cmds
      | some (_, _, some _) => IO.println s!"M\\t{tag}\\tstart\\tthe module has a start function"
      | none => IO.println s!"M\\t{tag}\\tinstantiate\\tinstantiation fails (or traps)"
"""


def probe():
    out = [PROBE_HEAD.replace("{fuel}", str(FUEL))]
    allsegs = {}
    for f, _ in FILES:
        segs, rows = load(f)
        allsegs[f] = (segs, rows)
        for seg in segs:
            if seg_reason(seg):
                continue
            data = (WORK / "json" / f / seg["wasm"]).read_bytes()
            tag = f"{f}/{seg['index']}"
            out.append(bytes_lean(f"b_{f}_{seg['index']}", data))
            cmds = runnable(seg)
            out.append(f"#eval {'probeS' if f in SPEC else 'probe'} {lean_str(tag)} b_{f}_{seg['index']} [\n  " +
                       ",\n  ".join(lean_cmd(r) for r in cmds) + "]\n")
        for r in rows:
            if r["status"] == "reject_candidate":
                out.append(bytes_lean(f"r_{f}_{r['line']}", (WORK / "json" / f / r["reject_wasm"]).read_bytes()))
                out.append(f"#eval probeReject {lean_str(r['id'])} r_{f}_{r['line']}\n")
    out.append(LINK_PROBE)
    probe_link(out)
    with tempfile.TemporaryDirectory() as td:
        p = pathlib.Path(td) / "Probe.lean"
        p.write_text("\n".join(out))
        if os.environ.get("WASM_WAST_KEEP_PROBE"):  # keep a copy of the probe file (debugging)
            shutil.copyfile(p, os.environ["WASM_WAST_KEEP_PROBE"])
        r = subprocess.run(["lake", "env", "lean", str(p)], cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("probe failed:\n" + r.stdout[-4000:] + r.stderr[-4000:])
    res = {"modules": {}, "cmds": {}, "rejects": {}, "link_decode": {}, "link_imports": {}}
    for line in r.stdout.splitlines():
        parts = line.split("\t")
        if parts[0] == "D":
            res["link_decode"].setdefault(parts[1], []).append(parts[2])
        elif parts[0] == "I":
            res["link_imports"][parts[1]] = [x for x in (parts[2] if len(parts) > 2 else "").split(",") if x]
        elif parts[0] == "M":
            res["modules"][parts[1]] = {"status": parts[2], "detail": parts[3] if len(parts) > 3 else ""}
        elif parts[0] == "R":
            res["rejects"][parts[1]] = parts[2]
        elif parts[0] == "P":
            res["cmds"][f"{parts[1]}/{parts[2]}"] = {"status": parts[3], "detail": parts[4] if len(parts) > 4 else ""}
    (WORK / "probe.json").write_text(json.dumps(res, indent=1))
    print(f"probe: {len(res['modules'])} modules, {len(res['cmds'])} commands -> {WORK / 'probe.json'}")


# ---------- emit ----------

def classify():
    pr = json.loads((WORK / "probe.json").read_text())
    files = []
    for f, mod in FILES:
        segs, rows = load(f)
        byid = {r["id"]: r for r in rows}
        for seg in segs:
            tag = f"{f}/{seg['index']}"
            reason = seg_reason(seg)
            mres = pr["modules"].get(tag)
            if reason is None and (mres is None or mres["status"] != "ok"):
                reason = f"module: {mres['detail'] if mres else 'not probed'}"
            seg["reason"] = reason
            seg["kernel_reason"] = KERNEL_OUT.get(tag) if reason is None else None
            seg["kmem"] = reason is None and mres["detail"] not in ("", "0") and f not in SPEC
            seg["spec"] = f in SPEC
            run = runnable(seg) if reason is None else []
            stop = None
            kernel = []
            for k, r in enumerate(run):
                p = pr["cmds"].get(f"{tag}/{k}")
                row = byid[r["id"]]
                if p is None or p["status"] in ("error", "undetermined"):
                    stop = k
                    if p is not None:
                        row["status"] = "undetermined" if p["status"] == "undetermined" else "unsupported"
                        row["reason"] = p["detail"]
                    break
                row["observed"] = p["detail"]
                if seg["kernel_reason"] is not None:
                    row["status"], row["reason"] = "undetermined", seg["kernel_reason"]
                    if p["status"] == "mismatch":
                        row["status"], row["reason"] = "mismatch", "the interpreter's outcome differs from the expectation"
                    continue
                if p["status"] == "pass":
                    row["status"] = "proved"
                    row["k"] = len(kernel)
                elif p["status"] == "mismatch":
                    row["status"] = "mismatch"
                    row["reason"] = ("the specification's result set is not contained in the expectation" if seg["spec"]
                                     else "the interpreter's outcome differs from the expectation")
                kernel.append((r, p["status"] == "pass"))
            seg["kernel"] = kernel if seg["kernel_reason"] is None else []
            # Commands of the segment after a stop, or after a truncating command, are undetermined.
            cut = False
            for r in seg["cmds"]:
                row = byid[r["id"]]
                if cut and row.get("status") in ("candidate", "action", "proved"):
                    row["status"], row["reason"] = "undetermined", "an earlier action of the script did not run"
                    row.pop("k", None)
                if r.get("truncates") or (stop is not None and run and r is run[stop]):
                    cut = True
            if reason is not None:
                for r in seg["cmds"]:
                    row = byid[r["id"]]
                    if row.get("status") in ("candidate", "action"):
                        row["status"], row["reason"] = "unsupported", reason
        for r in rows:
            if r.get("status") == "candidate":
                r["status"], r["reason"] = "undetermined", "not run"
            if r.get("status") == "reject_candidate":
                got = pr.get("rejects", {}).get(r["id"])
                want = REJECT_WANT[r["type"]]
                if got is not None:
                    r["observed"] = {"validator": "decode? reads a module; validate? rejects it",
                                     "decoder": "decode? rejects the bytes",
                                     "accepts": "decode? reads a module; validate? accepts it"}[got]
                if got == want:
                    r["status"], r["reject"] = "proved", got
                elif got is None:
                    r["status"], r["reason"] = "undetermined", "not probed"
                else:
                    r["status"] = "mismatch"
                    r["reason"] = f"{r['type']} expects a {want} rejection; silmaril-lean: {r['observed']}"
        files.append((f, mod, segs, rows))
    return files


def emit():
    files = classify()
    report = {"schema": "silmaril.wasm-wast.report.v0.1",
              "spec": {"repo": "https://github.com/WebAssembly/spec", "rev": WT["WASM_SPEC_REV"],
                       "archive_sha256": WT["WASM_SPEC_SHA256"]},
              "converter": {"tool": "wasm-tools json-from-wast", "version": WT["WT_VERSION"],
                            "sha256": WT["WT_UPSTREAM_SHA256"]},
              "profile": f"{PROFILE_DET} for the returns_only/traps_only rows and the link.* rows of the linked files "
                         "(" + ", ".join(f"{f}.wast" for f, _ in LINK_FILES) + f"); {PROFILE_SPEC} for the "
                         "returns_allowed_all/traps_all/terminates_all rows of " + ", ".join(f"{f}.wast" for f, _ in FILES if f in SPEC),
              "assumptions": ["assert_return/assert_trap rows: the module is valid, has no imports and no start function, and its function exports have scalar types",
                              "assert_return/assert_trap rows: no host function (Det.noHost); claims are about Core reduction Step (profile neverFail)",
                              "assert_return/assert_trap rows: the script state: the store threads through the earlier actions of the same module, in order",
                              "assert_return/assert_trap rows: termination is witnessed by the kernel run; other runs reach the same normal form by determinism",
                              "returns_allowed_all/traps_all/terminates_all rows (" + ", ".join(f"{f}.wast" for f, _ in FILES if f in SPEC) + "): the same module "
                              "conditions; claims are about Core reduction Step (Profile.spec nd r) with no host function, for every $ND and relaxed choice "
                              "(rows state nd = true, r = default); every exported function is straight-line numeric (local.get 0 ... local.get (k-1); op), "
                              "so every run is described by Silmaril.Wasm.Execution.Core.StraightLine.{nf, reaches, not_diverges, extends_nf}; "
                              "nan:canonical = canonical NaN of either sign, nan:arithmetic = NaN with the quiet bit set, of either sign, "
                              "other expectations are exact bits",
                              "assert_invalid rows are tool-level (silmaril.shapes.wasm.wast.validator_rejects): silmaril-lean's decode? reads "
                              "the bytes wasm-tools wrote and silmaril-lean's validate? rejects the module; with validate?_complete, no module "
                              "the bytes encode is valid in silmaril-lean's ModuleOk (a transcription; not a claim about the specification)",
                              "linked-script rows (" + ", ".join(f"{f}.wast" for f, _ in LINK_FILES) + "; silmaril.shapes.wasm.wast.link.*): the "
                              "whole file is one script, from the context Init; claims are about Core reduction Step (profile neverFail) with no host "
                              "function (Det.noHost), after the actual runs of every earlier module, register and action of the file, in order "
                              "(stores persist across modules, also through imported memories, tables and globals); imports resolve by name to "
                              "exports of registered instances (resolve?, the reference interpreter's registry) and must have the import types "
                              "(ExternAddrOk); modules are allocated and their segments initialised by instantiateOnce?; start functions run as Core reduction",
                              "linked-script rows: host model: " + HOST_MODEL,
                              "linked-script assert_unlinkable rows (silmaril.shapes.wasm.wast.link.unlinkable): the module is valid and its imports "
                              "do not resolve by name, or resolve to addresses without the import types (ExternAddrOk, silmaril-lean's transcription "
                              "of Externaddr_ok); hence no Instantiate derivation for them (Unlinkable.not_instantiate)",
                              "linked-script assert_uninstantiable rows (silmaril.shapes.wasm.wast.link.uninstantiable): the module links and is "
                              "allocated, and its start function traps at every host-free normal form; a segment initialisation that traps makes "
                              "instantiateOnce? fail and has no shape (the script stops there)"],
              "files": [], "commands": []}
    imports = []
    for f, mod, segs, rows in files:
        sha = sha256(SPEC_CORE / f"{f}.wast")
        report["files"].append({"file": f"test/core/{f}.wast", "sha256": sha,
                                "modules": [{"index": s["index"], "line": s["line"],
                                             "wasm_sha256": sha256(WORK / "json" / f / s["wasm"]) if s["wasm"] else None,
                                             "status": "ok" if s["reason"] is None and s["kernel_reason"] is None
                                             else "unsupported" if s["reason"] else "undetermined",
                                             "reason": s["reason"] or s["kernel_reason"],
                                             **({"checker": "scriptSK" if s["spec"] else "scriptKM" if s["kmem"] else "scriptK"}
                                                if s["reason"] is None and s["kernel_reason"] is None else {})}
                                            for s in segs]})
        if any(seg["kernel"] for seg in segs) or any(r.get("reject") for r in rows):
            defs, thms = emit_file(f, mod, segs, rows, sha)
            (LEAN_DIR / mod).mkdir(parents=True, exist_ok=True)
            (LEAN_DIR / mod / "Defs.lean").write_text(defs)
            (LEAN_DIR / mod / "Thms.lean").write_text(thms)
            imports.append(f"Silmaril.Project.WasmWast.{mod}.Thms")
        else:
            for x in ("Defs.lean", "Thms.lean"):
                (LEAN_DIR / mod / x).unlink(missing_ok=True)
            if (LEAN_DIR / mod).is_dir():
                (LEAN_DIR / mod).rmdir()
        for r in rows:
            if r["status"] == "module":
                continue
            c = {k: r[k] for k in ("id", "file", "line", "type", "status") if k in r}
            if "action" in r:
                c["invoke"] = r["action"]["field"]
                c["args"] = [show_val(v) for v in r["action"]["args"]]
            if "expected" in r:
                c["expected"] = [show_val(v) for v in r["expected"]]
            if r["type"] == "assert_trap":
                c["expected"] = ["trap"]
                c["trap_text"] = r.get("text")
            if r["type"] in REJECT_WANT:
                c["expected"] = [r["type"].removeprefix("assert_")]
                c["text"] = r.get("text")
            for k in ("reason", "observed"):
                if k in r:
                    c[k] = r[k]
            if "seg" in r:
                c["module"] = r["seg"]
            if "reject_wasm" in r:
                c["module_type"] = r["module_type"]
                c["wasm_sha256"] = sha256(WORK / "json" / f / r["reject_wasm"])
                if r["status"] == "proved":
                    shape, _, checker = REJECT[r["reject"]]
                    c["problem"] = f"{NS}.{f}.l{r['line']}"
                    c["shape"] = shape
                    c["theorem"] = f"Silmaril.Project.WasmWast.{mod}.l{r['line']}"
                    c["strength"] = "tool"
                    c["checker"] = checker
            elif r["status"] == "proved" and segs[r["seg"]]["spec"]:
                c["problem"] = f"{NS}.{f}.l{r['line']}"
                c["shape"] = SPEC_SHAPE[r["type"]]
                c["theorem"] = f"Silmaril.Project.WasmWast.{mod}.l{r['line']}"
                c["strength"] = "all"
                c["profile"] = "Profile.spec"
                c["allowed"] = c["expected"]
                c["claims"] = [{"kind": "all", "shape": c["shape"], "problem": c["problem"], "theorem": c["theorem"]},
                               {"kind": "terminates", "shape": TERM_SHAPE, "problem": f"{NS}.{f}.l{r['line']}_terminates",
                                "theorem": f"Silmaril.Project.WasmWast.{mod}.l{r['line']}_terminates"}]
                c["checker"] = "scriptSK"
            elif r["status"] == "proved":
                kind = "returns_only" if r["type"] == "assert_return" else "traps_only"
                c["problem"] = f"{NS}.{f}.l{r['line']}"
                c["shape"] = f"silmaril.shapes.wasm.wast.{kind}"
                c["theorem"] = f"Silmaril.Project.WasmWast.{mod}.l{r['line']}"
                c["strength"] = "only"
                c["profile"] = "profile neverFail"
                c["allowed"] = c["expected"]
                c["claims"] = [{"kind": "only", "shape": c["shape"], "problem": c["problem"], "theorem": c["theorem"]}]
                c["checker"] = "scriptKM" if segs[r["seg"]]["kmem"] else "scriptK"
            report["commands"].append(c)
    emit_link(report, imports)
    groups = [f"{NS}.{f}" for f, mod in FILES + LINK_FILES if f"Silmaril.Project.WasmWast.{mod}.Thms" in imports]
    top = ("module\n\n" + "".join(f"public import {i}\n" for i in imports) +
           "\n/-! # WAST rows of the pinned spec test suite: every file of the slice\n\n"
           "Generated by `tools/wasm-wast/gen.py` (`docs/projects/wasm-wast.md`). The group "
           f"`{NS}` (a child of the root `silmaril.all`) has one group per file. -/\n\n"
           f"silmaril group {NS} (title := \"WAST commands of the WebAssembly spec test suite, kernel-checked\")\n"
           f"  (children := [{', '.join(groups)}])\n")
    (LEAN_DIR / "Thms.lean").write_text(top)
    counts = {}
    for c in report["commands"]:
        counts[c["status"]] = counts.get(c["status"], 0) + 1
    reasons = {}
    for c in report["commands"]:
        if c["status"] in ("unsupported", "undetermined"):
            key = f"{c['status']}: {c.get('reason')}"
            reasons[key] = reasons.get(key, 0) + 1
    report["counts"] = {"total": len(report["commands"]), **counts}
    report["reasons"] = dict(sorted(reasons.items(), key=lambda x: -x[1]))
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n")
    print(json.dumps(report["counts"]), file=sys.stderr)
    for k, v in report["reasons"].items():
        print(f"  {v:4d} {k}", file=sys.stderr)


def link_report_row(f, mod, r):
    """The report entry of a row of a linked file."""
    c = {k: r[k] for k in ("id", "file", "line", "type", "status") if k in r}
    c["script"] = "linked"
    if "action" in r:
        a = r["action"]
        if a["type"] == "get":
            c["get"] = a["field"]
        else:
            c["invoke"] = a["field"]
            c["args"] = [show_val(v) for v in a["args"]]
        if a.get("module"):
            c["on"] = f"${a['module']}"
    if "expected" in r:
        c["expected"] = [show_res(v) for v in r["expected"]]
    if r["type"] == "assert_trap":
        c["expected"] = ["trap"]
        c["trap_text"] = r.get("text")
    if r["type"] in ("assert_unlinkable", "assert_uninstantiable"):
        c["expected"] = [r["type"].removeprefix("assert_")]
        c["text"] = r.get("text")
        if "link_wasm" in r:
            c["module_type"] = r.get("module_type")
            c["wasm_sha256"] = sha256(WORK / "json" / f / r["link_wasm"])
    if r["type"] == "register":
        c["register"] = {"as": r["register"]["as"], "module": f"${r['register']['module']}" if r["register"]["module"] else "current"}
    if r["type"] in REJECT_WANT:
        c["expected"] = [r["type"].removeprefix("assert_")]
        c["text"] = r.get("text")
    for k in ("reason", "observed", "context"):
        if k in r:
            c[k] = r[k]
    if "reject_wasm" in r:
        c["module_type"] = r["module_type"]
        c["wasm_sha256"] = sha256(WORK / "json" / f / r["reject_wasm"])
        if r["status"] == "proved":
            shape, _, checker = REJECT[r["reject"]]
            c.update(problem=f"{NS}.{f}.l{r['line']}", shape=shape, theorem=f"Silmaril.Project.WasmWast.{mod}.l{r['line']}",
                     strength="tool", checker=checker)
    elif r["status"] == "proved":
        shape = LINK_SHAPE[r["type"]]
        c.update(problem=f"{NS}.{f}.l{r['line']}", shape=shape, theorem=f"Silmaril.Project.WasmWast.{mod}.l{r['line']}",
                 strength=LINK_STRENGTH[r["type"]], profile="profile neverFail", host=HOST_MODEL, checker="scriptLK")
        if r["type"] in ("assert_return", "assert_trap"):
            c["allowed"] = c["expected"]
        c["claims"] = [{"kind": LINK_STRENGTH[r["type"]], "shape": shape, "problem": c["problem"], "theorem": c["theorem"]}]
    return c


def emit_link_file(f, mod, items, rows, kernel, sha):
    ns = f"Silmaril.Project.WasmWast.{mod}"
    mods = [it for it, _ in kernel if it["kind"] in MODKINDS]
    rejects = [r for r in rows if r.get("reject") and r["status"] == "proved"]
    defs = [f"""module

public import Silmaril.Project.Shapes.WasmWastLink.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# WAST rows: `test/core/{f}.wast` of the WebAssembly spec test suite, as a linked script

Generated by `tools/wasm-wast/gen.py`; do not edit. The source is `test/core/{f}.wast` of
WebAssembly/spec at `{WT['WASM_SPEC_REV']}`
(SHA-256 `{sha}`).
Each module is the binary that wasm-tools {WT['WT_VERSION']} `json-from-wast` writes for it, read by
silmaril-lean's decoder (`decode?`, sound: `decode?_sound`). `mJ` is the module of the `J`-th
`(module …)` of the file and `uL` the module of the `assert_unlinkable` / `assert_uninstantiable` at
line `L`. `cmds` is the script in order, from the context `Init` (the closed module
`Spectest.module` registered as `"spectest"`): every module, `register`, action and module assertion
up to the first command the kernel does not run. An assertion that the kernel checks keeps its
claim; every other one is kept for the context only (`expect := none`, `claim := false`).{{rdoc}}
-/

@[expose] public section

namespace {ns}

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Project.Shapes.WasmWastLink
"""]
    defs[0] = defs[0].replace("{rdoc}", "" if not rejects else
        "\n\n`invalidL` / `malformedL` are the bytes of the module of the `assert_invalid` /\n"
        "`assert_malformed` at line `L`: the binary that wasm-tools writes for it.")
    for it in mods:
        v = link_mod_var(it)
        data = link_wasm(f, it)
        line = it["line"] if it["kind"] == "module" else it["row"]["line"]
        what = "module" if it["kind"] == "module" else f"module of the `assert_{it['kind']}`"
        defs.append(("set_option maxRecDepth 100000 in\n" if len(data) > 2000 else "") +
                    f"/-- The bytes of the {what} at line {line} (`{it['wasm']}`,\n"
                    f"SHA-256 `{sha256(WORK / 'json' / f / it['wasm'])}`). -/")
        defs.append(bytes_lean(f"bytes_{v}", data))
        defs.append(f"/-- The {what} at line {line}, as silmaril-lean's decoder reads it. -/\n"
                    f"def {v} : Module := (Silmaril.Wasm.Binary.Core.decode? bytes_{v}).getD {{}}\n")
    if mods:
        defs.append("/-- Every module of the script decodes (so `mJ`, `uL` are the decoder's readings, not the\n"
                    "default `{}` of `getD`). -/\n"
                    "def decodesB : Bool :=\n  [" + ", ".join(f"bytes_{link_mod_var(it)}" for it in mods) +
                    "].all fun b => (Silmaril.Wasm.Binary.Core.decode? b).isSome\n")
    rec = "set_option maxRecDepth 20000 in\n" if len(kernel) > 400 else ""
    defs.append(f"{rec}/-- The script that the kernel runs, in order. -/\n"
                f"def cmds : List Cmd := [\n  " + ",\n  ".join(lean_link_cmd(it, ok) for it, ok in kernel) + "]\n")
    thms = [f"""module

public import {ns}.Defs
public import Silmaril.Project.Shapes.WasmWastLink.Thms
public import Silmaril.Project.Shapes.WasmWast.Thms

/-!
# WAST rows: `test/core/{f}.wast`, a linked script answered by one kernel evaluation

Generated by `tools/wasm-wast/gen.py`; do not edit. `script` proves every claim of `cmds`
(`ScriptHolds.of_kernel`, one `decide +kernel` evaluation of `scriptLK`, which instantiates the
closed `Spectest.module`, then validates, links, instantiates and runs every command in order on
`KMem` stores; the claims are about `ByteArray` stores and host-free Core reduction). Each row
`{NS}.{f}.l<line>` is the command at line `<line>`: `assert_return`
(`silmaril.shapes.wasm.wast.link.returns_only`), `assert_trap` (`….link.traps_only`),
`assert_unlinkable` (`….link.unlinkable`) or `assert_uninstantiable` (`….link.uninstantiable`),
after the commands before it (`pre cmds k`). `decodes`: every module of the script is the
decoder's reading of its bytes (not the default `{{}}` of `getD`), from the same kernel
evaluation. The index fact `cmds[k]? = some …` of a row is checked by `kernel_rfl`.{{rthm}}
-/

@[expose] public section

namespace {ns}

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Project.Shapes.WasmWastLink
"""]
    thms[0] = thms[0].replace("{rthm}", "" if not rejects else
        "\n\nAn `assert_invalid` row (`silmaril.shapes.wasm.wast.validator_rejects`) or binary\n"
        "`assert_malformed` row (`….decoder_rejects`) is tool-level: silmaril-lean's validator (decoder)\n"
        "rejects the bytes, by one `decide +kernel` evaluation.")
    names = []
    if kernel:
        if mods:
            # One kernel evaluation decodes every module (`decodesB`) and runs the script: the
            # kernel's cache shares the decoding with the checker's unfolding of `mJ`.
            thms.append(f"/-- The kernel checker accepts the script, and every module decodes. -/\n"
                        f"theorem check : (decodesB && scriptLK {O} {FUEL} cmds) = true := by decide +kernel\n")
            thms.append("/-- Every module of the script is the decoder's reading of its bytes. -/\n"
                        "theorem decodes : decodesB = true := (Bool.and_eq_true_iff.mp check).1\n")
            thms.append(f"/-- Every claim of the script. -/\n"
                        f"theorem script : ScriptHolds {O} cmds := .of_kernel (Bool.and_eq_true_iff.mp check).2\n")
        else:
            thms.append(f"/-- The kernel checker accepts the script. -/\n"
                        f"theorem check : scriptLK {O} {FUEL} cmds = true := by decide +kernel\n")
            thms.append(f"/-- Every claim of the script. -/\n"
                        f"theorem script : ScriptHolds {O} cmds := .of_kernel check\n")
        for k, (it, ok) in enumerate(kernel):
            if not ok:
                continue
            row = it["row"]
            name = f"{NS}.{f}.l{row['line']}"
            names.append(name)
            t = row["type"]
            if t == "assert_return":
                head = (f"  silmaril.shapes.wasm.wast.link.returns_only (o := {O})\n"
                        f"  (pre := pre cmds {k}) (act := {lean_link_action(row)}) (vs := [{', '.join(it['expect'][1])}])\n")
                proof = f"script.returnsOnly {k} (by kernel_rfl)"
            elif t == "assert_trap":
                head = (f"  silmaril.shapes.wasm.wast.link.traps_only (o := {O})\n"
                        f"  (pre := pre cmds {k}) (act := {lean_link_action(row)})\n")
                proof = f"script.trapsOnly {k} (by kernel_rfl)"
            else:
                kind = t.removeprefix("assert_")
                head = (f"  silmaril.shapes.wasm.wast.link.{kind} (o := {O})\n"
                        f"  (pre := pre cmds {k}) (m := {link_mod_var(it)})\n")
                proof = f"script.{kind} {k} (by kernel_rfl)"
            thms.append(f"silmaril instance {name} (expect := \"THM\") :=\n{head}")
            thms.append(f"@[answers {lean_str(name)} thm] theorem l{row['line']} : {name} :=\n  {proof}\n")
    for r in rejects:
        L = r["line"]
        shape, lean, _ = REJECT[r["reject"]]
        var = f"{r['type'].removeprefix('assert_')}{L}"
        defs.append(f"/-- The bytes of the module of the `{r['type']}` at line {L} (`{r['reject_wasm']}`,\n"
                    f"SHA-256 `{sha256(WORK / 'json' / f / r['reject_wasm'])}`). -/")
        defs.append(bytes_lean(var, (WORK / "json" / f / r["reject_wasm"]).read_bytes()))
        name = f"{NS}.{f}.l{L}"
        names.append(name)
        thms.append(f"silmaril instance {name} (expect := \"THM\") :=\n  {shape} (b := {var})\n")
        thms.append(f"@[answers {lean_str(name)} thm] theorem l{L} : {name} :=\n"
                    f"  Silmaril.Project.Shapes.WasmWast.{lean}.of_kernel (by decide +kernel)\n")
    defs.append(f"end {ns}\n\nend\n")
    thms.append(f"end {ns}\n\nend\n")
    names.sort(key=lambda n: int(n.rsplit(".l", 1)[1]))
    thms.append(f"silmaril group {NS}.{f} (title := {lean_str(f'test/core/{f}.wast: the kernel-checked commands (linked script)')})\n"
                f"  (children := [\n    " + ",\n    ".join(names) + "])\n")
    return "\n".join(defs), "\n".join(thms)


def emit_link(report, imports):
    for f, mod, items, rows, kernel in classify_link(json.loads((WORK / "probe.json").read_text())):
        sha = sha256(SPEC_CORE / f"{f}.wast")
        report["files"].append({"file": f"test/core/{f}.wast", "sha256": sha, "script": "linked", "checker": "scriptLK",
                                "modules": [{"index": it["index"], "line": it["line"], "name": it["name"],
                                             "wasm_sha256": sha256(WORK / "json" / f / it["wasm"]) if it["wasm"] else None,
                                             "status": "run" if any(it is x for x, _ in kernel) else "not run"}
                                            for it in items if it["kind"] == "module"]})
        if kernel or any(r.get("reject") for r in rows):
            defs, thms = emit_link_file(f, mod, items, rows, kernel, sha)
            (LEAN_DIR / mod).mkdir(parents=True, exist_ok=True)
            (LEAN_DIR / mod / "Defs.lean").write_text(defs)
            (LEAN_DIR / mod / "Thms.lean").write_text(thms)
            imports.append(f"Silmaril.Project.WasmWast.{mod}.Thms")
        for r in rows:
            report["commands"].append(link_report_row(f, mod, r))


def emit_file(f, mod, segs, rows, sha):
    ns = f"Silmaril.Project.WasmWast.{mod}"
    spec = f in SPEC
    simp_ = "\npublic import Silmaril.Project.Shapes.WasmWastSpec.Defs" if spec else ""
    sopen = "\nopen Silmaril.Project.Shapes.WasmWastSpec" if spec else ""
    defs = [f"""module

public import Silmaril.Project.Shapes.WasmWast.Defs{simp_}
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# WAST rows: `test/core/{f}.wast` of the WebAssembly spec test suite

Generated by `tools/wasm-wast/gen.py`; do not edit. The source is `test/core/{f}.wast` of
WebAssembly/spec at `{WT['WASM_SPEC_REV']}`
(SHA-256 `{sha}`).
Each module is the binary that
wasm-tools {WT['WT_VERSION']} `json-from-wast` writes for it, read by silmaril-lean's decoder
(`decode?`, sound: `decode?_sound`). `mJ` is the module of the `J`-th `(module …)` of the file and
`cmdsJ` the commands after it that the kernel runs, in script order: an `assert_return` or
`assert_trap` that the kernel checks keeps its expectation; every other one is kept as an action
(`expect := none`) so that the store threads through it.{{sdoc}}{{rdoc}}
-/

@[expose] public section

namespace {ns}

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Project.Shapes.WasmWast{sopen}
"""]
    defs[0] = defs[0].replace("{sdoc}", "" if not spec else
        "\n\nThe commands are checked under the specification profile `Profile.spec` (`CmdS`,\n"
        "`….WasmWastSpec.Defs`): an `assert_return` expectation is one pattern per result, `nan:canonical`\n"
        "(`.canonicalNaN`), `nan:arithmetic` (`.arithmeticNaN`) or an exact value compared as bits (`.exact`).")
    rejects = [r for r in rows if r.get("reject") and r["status"] == "proved"]
    rdoc = ("" if not rejects else "\n\n`invalidL` / `malformedL` are the bytes of the module of the `assert_invalid` /\n"
            "`assert_malformed` at line `L`: the binary that wasm-tools writes for it.")
    defs[0] = defs[0].replace("{rdoc}", rdoc)
    kinds = {s["kmem"] for s in segs if s["reason"] is None and s["kernel"]}
    checker = ("(`ScriptHoldsS.of_kernel`, one `decide +kernel` evaluation of `scriptSK` per module, under\n"
               "`Profile.spec nd r` for every `nd` and `r`)") if spec else ("(`ScriptHolds.of_kernel`, one `decide +kernel` evaluation of `scriptK` per module)" if kinds == {False}
               else "(one `decide +kernel` evaluation per module: `ScriptHolds.of_kernelKM` evaluates `scriptKM`,\n"
               "which instantiates the module, including its data segments, and runs the commands on `KMem`\n"
               "stores; the claims are about `ByteArray` stores and Core reduction, by `scriptK_of_scriptKM`"
               + (")" if kinds == {True} else ";\nmodules without data segments use `ScriptHolds.of_kernel` and `scriptK`)"))
    rowdoc = (f"each row\n`{NS}.{f}.l<line>` is one `assert_return` (`silmaril.shapes.wasm.wast.returns_allowed_all`: every\n"
              "host-free normal form returns values in the allowed set, and some run reaches one) or `assert_trap`\n"
              "(`….traps_all`) at line `<line>` of the file, and `….l<line>_terminates`\n"
              "(`….terminates_all`) says that no run of it is infinite; both answered from it.") if spec else (
              f"each row\n`{NS}.{f}.l<line>` is one `assert_return` (`silmaril.shapes.wasm.wast.returns_only`) or\n"
              "`assert_trap` (`….traps_only`) at line `<line>` of the file, answered from it.")
    sthm = "\npublic import Silmaril.Project.Shapes.WasmWastSpec.Thms" if spec else ""
    thms = [f"""module

public import {ns}.Defs
public import Silmaril.Project.Shapes.WasmWast.Thms{sthm}

/-!
# WAST rows: `test/core/{f}.wast`, answered by kernel evaluation

Generated by `tools/wasm-wast/gen.py`; do not edit. `scriptJ` proves every command of `cmdsJ`
{checker}; {rowdoc}{{rthm}}
-/

@[expose] public section

namespace {ns}

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Project.Shapes.WasmWast{sopen}
"""]
    thms[0] = thms[0].replace("{rthm}", "" if not rejects else
        "\n\nAn `assert_invalid` row (`….validator_rejects`) or binary `assert_malformed` row\n"
        "(`….decoder_rejects`) is tool-level: silmaril-lean's validator (decoder) rejects the bytes, by one\n"
        "`decide +kernel` evaluation. It does not claim that the module is invalid (malformed) in the\n"
        "specification; see `ValidatorRejects.not_valid` for what follows from `validate?_complete`.")
    byid = {r["id"]: r for r in rows}
    for seg in segs:
        j = seg["index"]
        if seg["reason"] is not None or not seg["kernel"]:
            continue
        data = (WORK / "json" / f / seg["wasm"]).read_bytes()
        defs.append(f"/-- The bytes of the module at line {seg['line']} (`{seg['wasm']}`,\n"
                    f"SHA-256 `{sha256(WORK / 'json' / f / seg['wasm'])}`). -/")
        defs.append(bytes_lean(f"bytes{j}", data))
        defs.append(f"/-- The module at line {seg['line']}, as silmaril-lean's decoder reads it. -/\n"
                    f"def m{j} : Module := (Silmaril.Wasm.Binary.Core.decode? bytes{j}).getD {{}}\n")
        # Long list literals exceed the default recursion depth of the elaborator.
        rec = "set_option maxRecDepth 20000 in\n" if spec or len(seg["kernel"]) > 500 else ""
        defs.append(f"{rec}/-- The commands after line {seg['line']} that the kernel runs. -/\n"
                    f"def cmds{j} : List {'CmdS' if spec else 'Cmd'} := [\n  " +
                    ",\n  ".join(lean_cmd(r, ok) for r, ok in seg["kernel"]) + "]\n")
        thms.append(f"/-- The decoder reads the file's bytes as `m{j}`. -/\n"
                    f"theorem decode{j} : Silmaril.Wasm.Binary.Core.decode? bytes{j} = some m{j} :=\n"
                    f"  (Option.some_get (by decide +kernel :\n"
                    f"    (Silmaril.Wasm.Binary.Core.decode? bytes{j}).isSome = true)).symm.trans\n"
                    f"    (congrArg some (Option.get_eq_getD _))\n")
        if spec:
            thms.append(f"/-- The kernel checker accepts `cmds{j}`. -/\n"
                        f"theorem check{j} : scriptSK m{j} cmds{j} = true := by decide +kernel\n")
            thms.append(f"/-- Every command of `cmds{j}`, under `Profile.spec nd r`. -/\n"
                        f"theorem script{j} (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice) :\n"
                        f"    ScriptHoldsS nd r m{j} cmds{j} :=\n"
                        f"  .of_kernel check{j}\n")
        else:
            thms.append(f"/-- Every command of `cmds{j}`, by one kernel evaluation. -/\n"
                        f"theorem script{j} : ScriptHolds {O} m{j} cmds{j} :=\n"
                        f"  .{'of_kernelKM' if seg['kmem'] else 'of_kernel'} (fuel := {FUEL}) (by decide +kernel)\n")
        for k, (r, ok) in enumerate(seg["kernel"]):
            if not ok:
                continue
            row = byid[r["id"]]
            name = f"{NS}.{f}.l{row['line']}"
            act = f"⟨{lean_str(row['action']['field'])}, [{', '.join(row['lean_args'])}]⟩"
            if spec:
                if row["type"] == "assert_return":
                    thms.append(f"silmaril instance {name} (expect := \"THM\") :=\n"
                                f"  silmaril.shapes.wasm.wast.returns_allowed_all (nd := true) (r := {{}})\n"
                                f"  (m := m{j}) (pre := preS cmds{j} {k}) (act := {act}) (ps := [{', '.join(row['expect'][1])}])\n")
                    thms.append(f"@[answers {lean_str(name)} thm] theorem l{row['line']} : {name} :=\n"
                                f"  (script{j} true {{}}).returnsAllowedAll {k} (by decide +kernel)\n")
                else:
                    thms.append(f"silmaril instance {name} (expect := \"THM\") :=\n"
                                f"  silmaril.shapes.wasm.wast.traps_all (nd := true) (r := {{}})\n"
                                f"  (m := m{j}) (pre := preS cmds{j} {k}) (act := {act})\n")
                    thms.append(f"@[answers {lean_str(name)} thm] theorem l{row['line']} : {name} :=\n"
                                f"  (script{j} true {{}}).trapsAll {k} (by decide +kernel)\n")
                thms.append(f"silmaril instance {name}_terminates (expect := \"THM\") :=\n"
                            f"  silmaril.shapes.wasm.wast.terminates_all (nd := true) (r := {{}})\n"
                            f"  (m := m{j}) (pre := preS cmds{j} {k}) (act := {act})\n")
                thms.append(f"@[answers {lean_str(name + '_terminates')} thm] theorem l{row['line']}_terminates :\n"
                            f"    {name}_terminates :=\n"
                            f"  (script{j} true {{}}).terminatesAll (cmd := {lean_cmd(r, ok)}) {k}\n"
                            f"    (by decide +kernel)\n")
            elif row["type"] == "assert_return":
                vs = ", ".join(row["expect"][1])
                thms.append(f"silmaril instance {name} (expect := \"THM\") :=\n"
                            f"  silmaril.shapes.wasm.wast.returns_only (o := {O})\n"
                            f"  (m := m{j}) (pre := pre cmds{j} {k}) (act := {act}) (vs := [{vs}])\n")
                thms.append(f"@[answers {lean_str(name)} thm] theorem l{row['line']} : {name} :=\n"
                            f"  script{j}.returnsOnly {k} rfl\n")
            else:
                thms.append(f"silmaril instance {name} (expect := \"THM\") :=\n"
                            f"  silmaril.shapes.wasm.wast.traps_only (o := {O})\n"
                            f"  (m := m{j}) (pre := pre cmds{j} {k}) (act := {act})\n")
                thms.append(f"@[answers {lean_str(name)} thm] theorem l{row['line']} : {name} :=\n"
                            f"  script{j}.trapsOnly {k} rfl\n")
    for r in rejects:
        L = r["line"]
        shape, lean, _ = REJECT[r["reject"]]
        var = f"{r['type'].removeprefix('assert_')}{L}"
        data = (WORK / "json" / f / r["reject_wasm"]).read_bytes()
        defs.append(f"/-- The bytes of the module of the `{r['type']}` at line {L} (`{r['reject_wasm']}`,\n"
                    f"SHA-256 `{sha256(WORK / 'json' / f / r['reject_wasm'])}`). -/")
        defs.append(bytes_lean(var, data))
        name = f"{NS}.{f}.l{L}"
        thms.append(f"silmaril instance {name} (expect := \"THM\") :=\n"
                    f"  {shape} (b := {var})\n")
        proof = "(by decide +kernel)"
        thms.append(f"@[answers {lean_str(name)} thm] theorem l{L} : {name} :=\n"
                    f"  {lean}.of_kernel {proof}\n")
    defs.append(f"end {ns}\n\nend\n")
    thms.append(f"end {ns}\n\nend\n")
    names = [f"{NS}.{f}.l{byid[r['id']]['line']}{x}" for seg in segs for r, ok in seg["kernel"] if ok
             for x in (("", "_terminates") if spec else ("",))]
    names += [f"{NS}.{f}.l{r['line']}" for r in rejects]
    thms.append(f"silmaril group {NS}.{f} (title := {lean_str(f'test/core/{f}.wast: the kernel-checked commands')})\n"
                f"  (children := [\n    " + ",\n    ".join(names) + "])\n")
    return "\n".join(defs), "\n".join(thms)


# ---------- oracle ----------

def wast_val(s):
    t, v = s.split(":", 1)
    if t in ("f32", "f64") and re.fullmatch(r"[0-9]+", v):
        w = WIDTH[t]
        return f"({t}.const {'-' if int(v) >> (w - 1) else ''}nan:0x{int(v) & ((1 << (w - 9 if w == 32 else w - 12)) - 1):x})" \
            if is_nan(t, int(v)) else f"({t}.const {float_hex(t, int(v))})"
    return f"({t}.const {v})"


def is_nan(t, bits):
    if t == "f32":
        return (bits >> 23) & 0xFF == 0xFF and bits & 0x7FFFFF
    return (bits >> 52) & 0x7FF == 0x7FF and bits & 0xFFFFFFFFFFFFF


def float_hex(t, bits):
    import struct
    if t == "f32":
        x = struct.unpack("<f", struct.pack("<I", bits))[0]
    else:
        x = struct.unpack("<d", struct.pack("<Q", bits))[0]
    if x != x:
        raise ValueError("nan")
    if x in (float("inf"), float("-inf")):
        return "inf" if x > 0 else "-inf"
    return x.hex()


def fetch_wasmtime():
    """Install the pinned wasmtime 50.0.0 binary at its pins.sh path: download the release archive
    into a fresh empty directory, check the archive's SHA-256, extract only the `wasmtime` member
    (nothing in the archive is run), check the binary's SHA-256, then copy it into place."""
    dest = pathlib.Path(JCO["WASMTIME"])
    if dest.is_file():
        need(dest, JCO["WASMTIME_SHA256"], "wasmtime")
        print(f"fetch-wasmtime: {dest} present, SHA-256 {JCO['WASMTIME_SHA256']}")
        return
    member = f"wasmtime-v{JCO['WASMTIME_VERSION']}-x86_64-linux/wasmtime"
    with tempfile.TemporaryDirectory(prefix="wasm-wast-dl-") as td:
        arc = pathlib.Path(td) / "wasmtime.tar.xz"
        with urllib.request.urlopen(JCO["WASMTIME_URL"]) as r, open(arc, "wb") as out:
            shutil.copyfileobj(r, out)
        if sha256(arc) != JCO["WASMTIME_ARCHIVE_SHA256"]:
            sys.exit(f"gen.py: {JCO['WASMTIME_URL']} does not match its pinned SHA-256")
        with tarfile.open(arc, "r:xz") as t:
            m = t.getmember(member)
            if not m.isfile():
                sys.exit(f"gen.py: {member} is not a regular file in the archive")
            src = t.extractfile(m)
            binp = pathlib.Path(td) / "wasmtime"
            with open(binp, "wb") as out:
                shutil.copyfileobj(src, out)
        need(binp, JCO["WASMTIME_SHA256"], "the extracted wasmtime")
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(binp, dest)
        dest.chmod(0o755)
    print(f"fetch-wasmtime: {dest}, SHA-256 {JCO['WASMTIME_SHA256']}")


def oracle_scripts(rep):
    """The oracle's script for every command it runs, in order: (id, script text). The command's
    module (the same binary, as `(module binary …)`), the actions before it in the same module
    (not for the SPEC files, whose modules have no state), then the command. Deterministic in
    report.json and the converted JSON."""
    status = {c["id"]: c for c in rep["commands"]}
    for f, _ in FILES:
        segs, rows = load(f)
        for seg in segs:
            prev = []
            mod = None
            for r in seg["cmds"]:
                if r["type"] not in ("assert_return", "assert_trap", "action") or "lean_args" not in r:
                    continue
                c = status[r["id"]]
                if c["status"] not in ("proved", "mismatch") and "observed" not in c:
                    prev.append(r)
                    continue
                if mod is None:
                    mod = module_binary((WORK / "json" / f / seg["wasm"]).read_bytes())
                lines = [mod]
                # The modules of the SPEC files have no memory, table or global, and every function is
                # straight-line numeric (the kernel checker requires it; StraightLine.nf: the store is
                # unchanged), so an earlier action cannot affect a command: the script is the module
                # and the command. Elsewhere the earlier actions of the module come first.
                for p in ([] if f in SPEC else prev):
                    lines.append(f"(invoke {wast_str(p['action']['field'])} {' '.join(wast_val(show_val(v)) for v in p['action']['args'])})"
                                 if p["type"] == "action" else wast_cmd(p))
                lines.append(wast_cmd(r))
                yield r["id"], "\n".join(lines) + "\n"
                prev.append(r)
        # Rejections: the same bytes as the row, as `(module binary …)`, under the same assertion.
        for r in rows:
            if "reject_wasm" in r and status[r["id"]]["status"] in ("proved", "mismatch"):
                yield r["id"], reject_script(r["type"], (WORK / "json" / f / r["reject_wasm"]).read_bytes(), r.get("text", ""))
    for f, _ in LINK_FILES:
        _, rows = load_link(f)
        for r in rows:
            if "reject_wasm" in r and status[r["id"]]["status"] in ("proved", "mismatch"):
                yield r["id"], reject_script(r["type"], (WORK / "json" / f / r["reject_wasm"]).read_bytes(), r.get("text", ""))


def module_binary(data):
    return '(module binary "' + "".join(f"\\{b:02x}" for b in data) + '")'


def wast_res(v):
    """An expected result in WAST text, as the file writes it."""
    t, x = v["type"], v.get("value")
    if t == "refnull":
        return "(ref.null)"
    if t in ("externref", "funcref", "anyref", "exnref") and x == "null":
        return f"(ref.null {t.removesuffix('ref')})"
    if t == "funcref" and x is None:
        return "(ref.func)"
    if t == "externref" and x is not None:
        return f"(ref.extern {x})"
    return wast_val(show_val(v))


def wast_link_action(r):
    a = r["action"]
    on = f" ${a['module']}" if a.get("module") else ""
    if a["type"] == "get":
        return f"(get{on} {wast_str(a['field'])})"
    return f"(invoke{on} {wast_str(a['field'])} {' '.join(wast_val(show_val(v)) for v in a['args'])})".replace(" )", ")")


def link_ran(c):
    return c["status"] in ("proved", "mismatch", "context") or "observed" in c


def link_selected(c):
    return c.get("script") == "linked" and "reject_wasm" not in c and \
        (c["status"] in ("proved", "mismatch") or "observed" in c)


def oracle_link_scripts(rep):
    """One script per linked file: every command the kernel ran, in order, as the file writes it
    (modules as `(module $name? binary …)` of the same bytes, `register`, actions and assertions
    with their original expectations, module assertions). The oracle runs it once; a command passes
    when wasmtime gets past its line. Yields (file, [(id, script line)], text). Deterministic in
    report.json and the converted JSON."""
    status = {c["id"]: c for c in rep["commands"]}
    for f, _ in LINK_FILES:
        items, _ = load_link(f)
        lines, ids, pending = [], [], []
        for it in items:
            if it["kind"] == "module":
                if it.get("stop"):
                    break
                nm = f" ${it['name']}" if it["name"] else ""
                pending.append(module_binary(link_wasm(f, it)).replace("(module ", f"(module{nm} ", 1))
                continue
            r = it["row"]
            c = status[r["id"]]
            if not link_ran(c):
                break
            lines += pending
            pending = []
            k = it["kind"]
            if k == "register":
                lines.append(f"(register {wast_str(it['as'])}{' $' + it['target'] if it['target'] else ''})")
            elif k == "unlinkable":
                lines.append(f"(assert_unlinkable {module_binary(link_wasm(f, it))} {wast_str(r.get('text', ''))})")
            elif k == "uninstantiable":
                # The file writes `(assert_trap (module …) "…")` (wasm-tools: `assert_uninstantiable`).
                lines.append(f"(assert_trap {module_binary(link_wasm(f, it))} {wast_str(r.get('text', ''))})")
            elif r["type"] == "assert_return":
                lines.append(f"(assert_return {wast_link_action(r)}{''.join(' ' + wast_res(v) for v in r.get('expected', []))})")
            elif r["type"] == "assert_trap":
                lines.append(f"(assert_trap {wast_link_action(r)} {wast_str(r.get('text', ''))})")
            else:
                lines.append(wast_link_action(r))
            if link_selected(c):
                ids.append((r["id"], len(lines)))
        if ids:
            yield f, ids, "\n".join(lines) + "\n"


def reject_script(kind, data, text):
    return f"({kind} {module_binary(data)} {wast_str(text)})\n"


def text_sha256(t):
    return hashlib.sha256(t.encode()).hexdigest()


def oracle_counts(results):
    proved = [x for x in results if x["silmaril"] == "proved"]
    native = [x for x in results if x["silmaril"] != "proved"]
    return {"run": len(results), "oracle_pass": sum(x["oracle"] == "pass" for x in results),
            "kernel_proved": len(proved), "agree_with_kernel": sum(x["oracle"] == "pass" for x in proved),
            "native_only": len(native), "agree_with_native_run": sum(x["oracle"] == "pass" for x in native)}


def provenance():
    """What the oracle run depends on, from the pins (checked against the installed files)."""
    return {"tool": "wasmtime", "version": JCO["WASMTIME_VERSION"], "url": JCO["WASMTIME_URL"],
            "archive_sha256": JCO["WASMTIME_ARCHIVE_SHA256"], "sha256": JCO["WASMTIME_SHA256"],
            "command": "wasmtime wast SCRIPT", "pins": "tools/wasm-jco/tests/pins.sh"}


def inputs(rep):
    return {"spec": rep["spec"], "converter": rep["converter"], "report_sha256": sha256(REPORT),
            "files": [{"file": x["file"], "sha256": x["sha256"]} for x in rep["files"]]}


def scrub(err):
    """Drop local paths from wasmtime's messages."""
    return err.replace(str(SPEC_CORE), "test/core").replace(str(pathlib.Path.home()), "~")


def oracle():
    """Run wasmtime 50.0.0 `wast` on one small script per command (`oracle_scripts`). A command
    passes when wasmtime accepts the script. With `--check` (CI), oracle.json is not rewritten:
    the fresh record goes to WORK/oracle.check.json, and the run fails if any command fails under
    wasmtime, or if its verdicts, scripts or kernel statuses differ from the committed record."""
    if not pathlib.Path(JCO["WASMTIME"]).is_file():
        fetch_wasmtime()
    need(JCO["WASMTIME"], JCO["WASMTIME_SHA256"], "wasmtime")
    rep = json.loads(REPORT.read_text())
    ver = subprocess.run([JCO["WASMTIME"], "--version"], capture_output=True, text=True, check=True).stdout.strip()
    res = {"schema": "silmaril.wasm-wast.oracle.v0.2",
           "generated_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
           "host": f"{platform.system()} {platform.machine()}",
           "oracle": {**provenance(), "version_output": ver}, "inputs": inputs(rep), "results": []}
    status = {c["id"]: c["status"] for c in rep["commands"]}
    kinds = {c["id"]: c["type"] for c in rep["commands"]}
    with tempfile.TemporaryDirectory() as td:
        script = pathlib.Path(td) / "t.wast"
        for cid, text in oracle_scripts(rep):
            script.write_text(text)
            pr = subprocess.run([JCO["WASMTIME"], "wast", str(script)], capture_output=True, text=True)
            # A rejection row passes when wasmtime rejects the module. wasmtime also compares its
            # own message with the file's (substring); when only the wording differs, the row
            # passes and the record says so (`message`), with wasmtime's error.
            worded = pr.returncode != 0 and kinds.get(cid) in REJECT_WANT and \
                re.search(r"(assert_invalid|assert_malformed): expected \".*\", got \"", pr.stderr) is not None
            res["results"].append({"id": cid, "oracle": "pass" if pr.returncode == 0 or worded else "fail",
                                   "script_sha256": text_sha256(text), "silmaril": status[cid],
                                   **({"message": "differs", "stderr": scrub(pr.stderr)[-400:]} if worded else
                                      {"stderr": scrub(pr.stderr)[-400:]} if pr.returncode else {})})
        # Linked files: one run of the whole script; a command passes when wasmtime gets past it.
        for f, ids, text in oracle_link_scripts(rep):
            script.write_text(text)
            pr = subprocess.run([JCO["WASMTIME"], "wast", str(script)], capture_output=True, text=True)
            m = re.search(r"t\.wast:(\d+):", pr.stderr)
            bad = int(m.group(1)) if pr.returncode and m else (0 if pr.returncode else None)
            for cid, line in ids:
                ok = bad is None or line < bad
                res["results"].append({"id": cid, "oracle": "pass" if ok else "fail", "script": f"linked:{f}",
                                       "script_line": line, "script_sha256": text_sha256(text), "silmaril": status[cid],
                                       **({} if ok else {"stderr": scrub(pr.stderr)[-400:]})})
    res["counts"] = oracle_counts(res["results"])
    # The whole upstream files, unmodified, as a baseline of the oracle itself.
    res["files"] = []
    for f, _ in FILES + LINK_FILES:
        pr = subprocess.run([JCO["WASMTIME"], "wast", str(SPEC_CORE / f"{f}.wast")], capture_output=True, text=True)
        res["files"].append({"file": f"test/core/{f}.wast", "sha256": sha256(SPEC_CORE / f"{f}.wast"),
                             "oracle": "pass" if pr.returncode == 0 else "fail",
                             **({"stderr": scrub(pr.stderr)[-400:]} if pr.returncode else {})})
    print(json.dumps(res["counts"]), file=sys.stderr)
    if "--check" not in sys.argv:
        ORACLE.write_text(json.dumps(res, indent=1) + "\n")
        return
    out = WORK / "oracle.check.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=1) + "\n")
    old = json.loads(ORACLE.read_text())
    key = lambda x: (x["id"], x["oracle"], x["script_sha256"], x["silmaril"])
    bad = [f"{x['id']}: wasmtime fails: {x.get('stderr', '')[-200:]!r}" for x in res["results"] if x["oracle"] != "pass"]
    new_k, old_k = {key(x) for x in res["results"]}, {key(x) for x in old["results"]}
    bad += [f"not in oracle.json: {k}" for k in sorted(new_k - old_k)]
    bad += [f"in oracle.json, not re-obtained: {k}" for k in sorted(old_k - new_k)]
    fk = lambda x: (x["file"], x["sha256"], x["oracle"])
    if [fk(x) for x in res["files"]] != [fk(x) for x in old.get("files", [])]:
        bad.append("the verdicts on the unmodified upstream files differ from oracle.json")
    print(f"oracle --check: {len(res['results'])} commands re-run, {res['counts']['oracle_pass']} pass; record {out}")
    if bad:
        print("\n".join(f"oracle --check: DISAGREE {b}" for b in bad[:50]), file=sys.stderr)
        sys.exit(1)
    print("oracle --check: ok (every command passes; verdicts, scripts and statuses equal oracle.json)")


def regress():
    """The oracle's own regression: wasmtime must reject a deliberately wrong expectation.

    * Committed scripts `regress/wrong-*.wast`: each has exactly one directive marked `;; WRONG`
      (a wrong expectation). wasmtime must fail, and on that directive's line, so that the
      failure is the wrong expectation and not, say, a parse error. `regress/right-*.wast` (the
      same modules, right expectations) must pass, so the failures are not a broken wasmtime.
    * Generated scripts: the first `assert_return` and the first `assert_invalid` script of
      `oracle_scripts`, with the expectation made wrong (the result value plus one; the module
      replaced by a valid empty one), and the first `nan:arithmetic` expectation of an `add` of a
      non-canonical NaN, made `nan:canonical`; and in the linked script of linking.wast, the
      first `assert_return` on a module that imports from another registered module, plus one
      (wasmtime must fail on that line). wasmtime must fail on each, so `oracle`'s scripts can
      fail. The committed `wrong-linked-state.wast` writes a memory and a global through imports
      from one module and reads them from another.
    Exits 1 if any wrong expectation is accepted or any control fails."""
    if not pathlib.Path(JCO["WASMTIME"]).is_file():
        fetch_wasmtime()
    need(JCO["WASMTIME"], JCO["WASMTIME_SHA256"], "wasmtime")
    bad, n = [], 0

    def run(path):
        return subprocess.run([JCO["WASMTIME"], "wast", str(path)], capture_output=True, text=True)

    for p in sorted(REGRESS.glob("*.wast")):
        n += 1
        r = run(p)
        if p.name.startswith("right-"):
            if r.returncode != 0:
                bad.append(f"{p.name}: the control fails: {scrub(r.stderr)[-300:]!r}")
            continue
        marks = [i + 1 for i, line in enumerate(p.read_text().splitlines()) if ";; WRONG" in line]
        if len(marks) != 1:
            bad.append(f"{p.name}: {len(marks)} `;; WRONG` marks, want 1")
        elif r.returncode == 0:
            bad.append(f"{p.name}: wasmtime ACCEPTS a wrong expectation (line {marks[0]})")
        elif f"{p.name}:{marks[0]}" not in r.stderr:
            bad.append(f"{p.name}: wasmtime fails, but not on the wrong line {marks[0]}: {scrub(r.stderr)[-300:]!r}")
    rep = json.loads(REPORT.read_text())
    byid = {c["id"]: c for c in rep["commands"]}
    have_json = all((WORK / "json" / f / f"{f}.json").is_file() for f, _ in FILES + LINK_FILES)
    if not have_json:
        bad.append(f"converted JSON missing under {WORK / 'json'} (run `gen.py convert`)")
    else:
        mutants = {}
        for cid, text in oracle_scripts(rep):
            t = byid[cid]["type"]
            last = text.rstrip("\n").split("\n")[-1]
            # A NaN pattern made wrong: `nan:arithmetic` -> `nan:canonical` on an `add` of a
            # non-canonical NaN (the spec allows any arithmetic NaN; wasmtime keeps the payload).
            if (t == "assert_return" and "nan" not in mutants and byid[cid].get("invoke") == "add"
                    and last.endswith(".const nan:arithmetic))") and "nan:0x" in last):
                mutants["nan"] = (cid, text.rstrip("\n")[: -len(last)] + last.replace("nan:arithmetic))", "nan:canonical))") + "\n")
            if t == "assert_return" and t not in mutants:
                m = re.search(r"\((i32|i64)\.const (-?[0-9]+)\)\)$", last)
                if m:
                    w = WIDTH[m.group(1)]
                    wrong = last[:m.start()] + f"({m.group(1)}.const {(int(m.group(2)) + 1) % (1 << w)}))"
                    mutants[t] = (cid, text.rstrip("\n")[: -len(last)] + wrong + "\n")
            elif t == "assert_invalid" and t not in mutants:
                mutants[t] = (cid, reject_script("assert_invalid", bytes.fromhex("0061736d01000000"), byid[cid].get("text") or ""))
        # Cross-module state made wrong: in the linked script of linking.wast, the first
        # `assert_return` on the current module when that module imports from a registered
        # module other than spectest (so its result depends on another module's state), plus
        # one, with the script cut after it. wasmtime must fail on that line.
        for f, ids, text in oracle_link_scripts(rep):
            if f != "linking" or "linked" in mutants:
                continue
            lines = text.rstrip("\n").split("\n")
            for cid, ln in ids:
                c, line = byid[cid], lines[ln - 1]
                ctx = c.get("context") or {}
                m = re.search(r"\((i32|i64)\.const (-?[0-9]+)\)\)$", line)
                if (c["type"] == "assert_return" and m and ctx.get("current") and c.get("on") == ctx["current"]
                        and any(not x.startswith("spectest.") for x in ctx.get("current_imports", []))):
                    w = WIDTH[m.group(1)]
                    wrong = line[:m.start()] + f"({m.group(1)}.const {(int(m.group(2)) + 1) % (1 << w)}))"
                    mutants["linked"] = (f"{cid} (script line {ln})", "\n".join(lines[:ln - 1] + [wrong]) + "\n", ln)
                    break
        with tempfile.TemporaryDirectory() as td:
            if "linked" not in mutants:
                bad.append("no linked script to mutate")
            else:
                cid, text, line = mutants.pop("linked")
                path = pathlib.Path(td) / "wrong.wast"
                path.write_text(text)
                n += 1
                r = run(path)
                if r.returncode == 0:
                    bad.append(f"{cid} (linked) with a wrong expectation: wasmtime ACCEPTS it")
                elif f"wrong.wast:{line}" not in r.stderr:
                    bad.append(f"{cid} (linked): wasmtime fails, but not on the wrong line {line}: {scrub(r.stderr)[-300:]!r}")
            for t in ("assert_return", "assert_invalid", "nan"):
                if t not in mutants:
                    bad.append(f"no {t} script to mutate")
                    continue
                cid, text = mutants[t]
                path = pathlib.Path(td) / "wrong.wast"
                path.write_text(text)
                n += 1
                if run(path).returncode == 0:
                    bad.append(f"{cid} ({t}) with a wrong expectation: wasmtime ACCEPTS it")
    print(f"regress: {n} scripts run ({len(list(REGRESS.glob('wrong-*.wast')))} committed wrong, "
          f"{len(list(REGRESS.glob('right-*.wast')))} committed controls, 4 generated wrong)")
    if bad:
        print("\n".join(f"regress: FAIL {b}" for b in bad), file=sys.stderr)
        sys.exit(1)
    print("regress: ok (every wrong expectation is rejected by wasmtime; every control passes)")


def verify():
    """Re-check oracle.json against the current pins and report.json, without running wasmtime:
    the recorded tool provenance equals the pins; report.json and the spec files have the
    recorded SHA-256; the commands run are exactly those the report selects for the oracle, with
    the report's statuses; the counts follow from the results. With the converted JSON of
    `convert` present (or required by `--scripts`), every script is regenerated and its SHA-256
    compared. Exits 1 on any difference."""
    rep = json.loads(REPORT.read_text())
    orc = json.loads(ORACLE.read_text())
    bad = []

    def check(ok, what):
        if not ok:
            bad.append(what)

    check(orc.get("schema") == "silmaril.wasm-wast.oracle.v0.2", f"schema {orc.get('schema')}")
    for k, v in provenance().items():
        check(orc.get("oracle", {}).get(k) == v, f"oracle.{k}: recorded {orc.get('oracle', {}).get(k)!r}, pinned {v!r}")
    check(orc.get("oracle", {}).get("version_output", "").startswith(f"wasmtime {JCO['WASMTIME_VERSION']}"),
          "oracle.version_output")
    check(orc.get("inputs") == inputs(rep), "inputs (report.json SHA-256, spec pin, converter or file SHA-256 differ)")
    check([f["sha256"] for f in orc.get("files", [])] == [f["sha256"] for f in rep["files"]], "files: spec file SHA-256")
    status = {c["id"]: c["status"] for c in rep["commands"]}
    want = [c["id"] for c in rep["commands"] if c["status"] in ("proved", "mismatch") or "observed" in c]
    got = [x["id"] for x in orc["results"]]
    check(sorted(got) == sorted(want) and len(set(got)) == len(got),
          f"results: {len(got)} ids recorded, {len(want)} selected by report.json")
    for x in orc["results"]:
        check(status.get(x["id"]) == x["silmaril"], f"{x['id']}: silmaril status {x['silmaril']} vs report {status.get(x['id'])}")
    check(orc.get("counts") == oracle_counts(orc["results"]), "counts do not follow from the results")
    have_json = all((WORK / "json" / f / f"{f}.json").is_file() for f, _ in FILES + LINK_FILES)
    if "--scripts" in sys.argv and not have_json:
        bad.append(f"--scripts: converted JSON missing under {WORK / 'json'} (run `gen.py convert`)")
    scripts = "skipped (no converted JSON; `gen.py convert` enables it)"
    if have_json:
        rec = {x["id"]: x["script_sha256"] for x in orc["results"]}
        n = 0
        for cid, text in oracle_scripts(rep):
            n += 1
            check(rec.get(cid) == text_sha256(text), f"{cid}: script SHA-256 differs")
        nl = 0
        for f, ids, text in oracle_link_scripts(rep):
            nl += 1
            for cid, _ in ids:
                n += 1
                check(rec.get(cid) == text_sha256(text), f"{cid}: linked script ({f}) SHA-256 differs")
        check(n == len(rec), f"scripts: {n} regenerated, {len(rec)} recorded")
        scripts = f"{n} regenerated ({nl} linked-file scripts), SHA-256 compared"
    c = orc["counts"]
    print(f"verify: oracle.json of {orc.get('generated_at')}, wasmtime {orc['oracle']['version']} "
          f"(binary SHA-256 {orc['oracle']['sha256']}); {c['run']} commands, "
          f"{c['agree_with_kernel']}/{c['kernel_proved']} kernel-proved agree, "
          f"{c['agree_with_native_run']}/{c['native_only']} native-only agree; scripts: {scripts}")
    if bad:
        print("\n".join(f"verify: MISMATCH {b}" for b in bad[:50]), file=sys.stderr)
        sys.exit(1)
    print("verify: ok")


def wast_cmd(r):
    a = r["action"]
    inv = f"(invoke {wast_str(a['field'])} {' '.join(wast_val(show_val(v)) for v in a['args'])})"
    if r["type"] == "assert_trap":
        return f"(assert_trap {inv} {wast_str(r.get('text', ''))})"
    if r["type"] == "assert_return":
        return f"(assert_return {inv} {' '.join(wast_val(show_val(v)) for v in r.get('expected', []))})"
    return inv


def site():
    if len(sys.argv) < 3:
        sys.exit("usage: gen.py site DIR")
    d = pathlib.Path(sys.argv[2]) / "wast"
    d.mkdir(parents=True, exist_ok=True)
    for p in (REPORT, ORACLE):
        if p.is_file():
            (d / p.name).write_bytes(p.read_bytes())
            print(f"site: {d / p.name}")


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else "all"
    if cmd == "site":
        return site()
    steps = {"convert": [convert], "probe": [probe], "emit": [emit], "oracle": [oracle],
             "fetch-wasmtime": [fetch_wasmtime], "verify": [verify], "regress": [regress],
             "all": [convert, probe, emit, oracle]}
    if cmd not in steps:
        sys.exit(__doc__)
    for s in steps[cmd]:
        s()


if __name__ == "__main__":
    main()
