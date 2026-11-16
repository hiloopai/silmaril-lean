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
FILES = [("i32", "I32"), ("i64", "I64"), ("int_exprs", "IntExprs"), ("fac", "Fac"), ("traps", "Traps"), ("address", "Address")]
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
    for f, _ in FILES:
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


def show_val(v):
    """`type:bits` with the bits as an unsigned decimal (as the interpreter's observation is
    printed), or the WAST text of a pattern such as `nan:canonical`."""
    t, x = v["type"], v.get("value")
    if t in WIDTH and re.fullmatch(r"-?[0-9]+", str(x)):
        return f"{t}:{int(x) % (1 << WIDTH[t])}"
    return f"{t}:{x}"


def lean_str(s):
    return json.dumps(s, ensure_ascii=False)


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


# ---------- probe ----------

PROBE_HEAD = """import Silmaril.Project.Shapes.WasmWast.Defs
import Silmaril.Wasm.Binary.Core.Decode
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Project.Shapes.WasmWast
open Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

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
            out.append(f"#eval probe {lean_str(tag)} b_{f}_{seg['index']} [\n  " +
                       ",\n  ".join(lean_cmd(r) for r in cmds) + "]\n")
        for r in rows:
            if r["status"] == "reject_candidate":
                out.append(bytes_lean(f"r_{f}_{r['line']}", (WORK / "json" / f / r["reject_wasm"]).read_bytes()))
                out.append(f"#eval probeReject {lean_str(r['id'])} r_{f}_{r['line']}\n")
    with tempfile.TemporaryDirectory() as td:
        p = pathlib.Path(td) / "Probe.lean"
        p.write_text("\n".join(out))
        r = subprocess.run(["lake", "env", "lean", str(p)], cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("probe failed:\n" + r.stdout[-4000:] + r.stderr[-4000:])
    res = {"modules": {}, "cmds": {}, "rejects": {}}
    for line in r.stdout.splitlines():
        parts = line.split("\t")
        if parts[0] == "M":
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
            seg["kmem"] = reason is None and mres["detail"] not in ("", "0")
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
                    row["reason"] = "the interpreter's outcome differs from the expectation"
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
              "profile": "profile neverFail (deterministic: canonical NaNs, $ND = false, grow fails only when impossible)",
              "assumptions": ["assert_return/assert_trap rows: the module is valid, has no imports and no start function, and its function exports have scalar types",
                              "assert_return/assert_trap rows: no host function (Det.noHost); claims are about Core reduction Step (profile neverFail)",
                              "assert_return/assert_trap rows: the script state: the store threads through the earlier actions of the same module, in order",
                              "assert_return/assert_trap rows: termination is witnessed by the kernel run; other runs reach the same normal form by determinism",
                              "assert_invalid rows are tool-level (silmaril.shapes.wasm.wast.validator_rejects): silmaril-lean's decode? reads "
                              "the bytes wasm-tools wrote and silmaril-lean's validate? rejects the module; with validate?_complete, no module "
                              "the bytes encode is valid in silmaril-lean's ModuleOk (a transcription; not a claim about the specification)"],
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
                                             **({"checker": "scriptKM" if s["kmem"] else "scriptK"}
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
            elif r["status"] == "proved":
                kind = "returns_only" if r["type"] == "assert_return" else "traps_only"
                c["problem"] = f"{NS}.{f}.l{r['line']}"
                c["shape"] = f"silmaril.shapes.wasm.wast.{kind}"
                c["theorem"] = f"Silmaril.Project.WasmWast.{mod}.l{r['line']}"
                c["strength"] = "only"
                c["checker"] = "scriptKM" if segs[r["seg"]]["kmem"] else "scriptK"
            report["commands"].append(c)
    groups = [f"{NS}.{f}" for f, mod in FILES if f"Silmaril.Project.WasmWast.{mod}.Thms" in imports]
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


def emit_file(f, mod, segs, rows, sha):
    ns = f"Silmaril.Project.WasmWast.{mod}"
    defs = [f"""module

public import Silmaril.Project.Shapes.WasmWast.Defs
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
(`expect := none`) so that the store threads through it.{{rdoc}}
-/

@[expose] public section

namespace {ns}

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Project.Shapes.WasmWast
"""]
    rejects = [r for r in rows if r.get("reject") and r["status"] == "proved"]
    rdoc = ("" if not rejects else "\n\n`invalidL` / `malformedL` are the bytes of the module of the `assert_invalid` /\n"
            "`assert_malformed` at line `L`: the binary that wasm-tools writes for it.")
    defs[0] = defs[0].replace("{rdoc}", rdoc)
    kinds = {s["kmem"] for s in segs if s["reason"] is None and s["kernel"]}
    checker = ("(`ScriptHolds.of_kernel`, one `decide +kernel` evaluation of `scriptK` per module)" if kinds == {False}
               else "(one `decide +kernel` evaluation per module: `ScriptHolds.of_kernelKM` evaluates `scriptKM`,\n"
               "which instantiates the module, including its data segments, and runs the commands on `KMem`\n"
               "stores; the claims are about `ByteArray` stores and Core reduction, by `scriptK_of_scriptKM`"
               + (")" if kinds == {True} else ";\nmodules without data segments use `ScriptHolds.of_kernel` and `scriptK`)"))
    thms = [f"""module

public import {ns}.Defs
public import Silmaril.Project.Shapes.WasmWast.Thms

/-!
# WAST rows: `test/core/{f}.wast`, answered by kernel evaluation

Generated by `tools/wasm-wast/gen.py`; do not edit. `scriptJ` proves every command of `cmdsJ`
{checker}; each row
`{NS}.{f}.l<line>` is one `assert_return` (`silmaril.shapes.wasm.wast.returns_only`) or
`assert_trap` (`….traps_only`) at line `<line>` of the file, answered from it.{{rthm}}
-/

@[expose] public section

namespace {ns}

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Project.Shapes.WasmWast
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
        defs.append(f"/-- The commands after line {seg['line']} that the kernel runs. -/\n"
                    f"def cmds{j} : List Cmd := [\n  " +
                    ",\n  ".join(lean_cmd(r, ok) for r, ok in seg["kernel"]) + "]\n")
        thms.append(f"/-- The decoder reads the file's bytes as `m{j}`. -/\n"
                    f"theorem decode{j} : Silmaril.Wasm.Binary.Core.decode? bytes{j} = some m{j} :=\n"
                    f"  (Option.some_get (by decide +kernel :\n"
                    f"    (Silmaril.Wasm.Binary.Core.decode? bytes{j}).isSome = true)).symm.trans\n"
                    f"    (congrArg some (Option.get_eq_getD _))\n")
        thms.append(f"/-- Every command of `cmds{j}`, by one kernel evaluation. -/\n"
                    f"theorem script{j} : ScriptHolds {O} m{j} cmds{j} :=\n"
                    f"  .{'of_kernelKM' if seg['kmem'] else 'of_kernel'} (fuel := {FUEL}) (by decide +kernel)\n")
        for k, (r, ok) in enumerate(seg["kernel"]):
            if not ok:
                continue
            row = byid[r["id"]]
            name = f"{NS}.{f}.l{row['line']}"
            act = f"⟨{lean_str(row['action']['field'])}, [{', '.join(row['lean_args'])}]⟩"
            if row["type"] == "assert_return":
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
    names = [f"{NS}.{f}.l{byid[r['id']]['line']}" for seg in segs for r, ok in seg["kernel"] if ok]
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
    module (the same binary, as `(module binary …)`), the actions before it in the same module,
    then the command. Deterministic in report.json and the converted JSON."""
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
                for p in prev:
                    lines.append(f"(invoke {lean_str(p['action']['field'])} {' '.join(wast_val(show_val(v)) for v in p['action']['args'])})"
                                 if p["type"] == "action" else wast_cmd(p))
                lines.append(wast_cmd(r))
                yield r["id"], "\n".join(lines) + "\n"
                prev.append(r)
        # Rejections: the same bytes as the row, as `(module binary …)`, under the same assertion.
        for r in rows:
            if "reject_wasm" in r and status[r["id"]]["status"] in ("proved", "mismatch"):
                yield r["id"], reject_script(r["type"], (WORK / "json" / f / r["reject_wasm"]).read_bytes(), r.get("text", ""))


def module_binary(data):
    return '(module binary "' + "".join(f"\\{b:02x}" for b in data) + '")'


def reject_script(kind, data, text):
    return f"({kind} {module_binary(data)} {lean_str(text)})\n"


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
    with tempfile.TemporaryDirectory() as td:
        script = pathlib.Path(td) / "t.wast"
        for cid, text in oracle_scripts(rep):
            script.write_text(text)
            pr = subprocess.run([JCO["WASMTIME"], "wast", str(script)], capture_output=True, text=True)
            res["results"].append({"id": cid, "oracle": "pass" if pr.returncode == 0 else "fail",
                                   "script_sha256": text_sha256(text), "silmaril": status[cid],
                                   **({"stderr": scrub(pr.stderr)[-400:]} if pr.returncode else {})})
    res["counts"] = oracle_counts(res["results"])
    # The whole upstream files, unmodified, as a baseline of the oracle itself.
    res["files"] = []
    for f, _ in FILES:
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
      replaced by a valid empty one). wasmtime must fail on each, so `oracle`'s scripts can fail.
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
    have_json = all((WORK / "json" / f / f"{f}.json").is_file() for f, _ in FILES)
    if not have_json:
        bad.append(f"converted JSON missing under {WORK / 'json'} (run `gen.py convert`)")
    else:
        mutants = {}
        for cid, text in oracle_scripts(rep):
            t = byid[cid]["type"]
            last = text.rstrip("\n").split("\n")[-1]
            if t == "assert_return" and t not in mutants:
                m = re.search(r"\((i32|i64)\.const (-?[0-9]+)\)\)$", last)
                if m:
                    w = WIDTH[m.group(1)]
                    wrong = last[:m.start()] + f"({m.group(1)}.const {(int(m.group(2)) + 1) % (1 << w)}))"
                    mutants[t] = (cid, text.rstrip("\n")[: -len(last)] + wrong + "\n")
            elif t == "assert_invalid" and t not in mutants:
                mutants[t] = (cid, reject_script("assert_invalid", bytes.fromhex("0061736d01000000"), byid[cid].get("text") or ""))
        with tempfile.TemporaryDirectory() as td:
            for t in ("assert_return", "assert_invalid"):
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
          f"{len(list(REGRESS.glob('right-*.wast')))} committed controls, 2 generated wrong)")
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
    have_json = all((WORK / "json" / f / f"{f}.json").is_file() for f, _ in FILES)
    if "--scripts" in sys.argv and not have_json:
        bad.append(f"--scripts: converted JSON missing under {WORK / 'json'} (run `gen.py convert`)")
    scripts = "skipped (no converted JSON; `gen.py convert` enables it)"
    if have_json:
        rec = {x["id"]: x["script_sha256"] for x in orc["results"]}
        n = 0
        for cid, text in oracle_scripts(rep):
            n += 1
            check(rec.get(cid) == text_sha256(text), f"{cid}: script SHA-256 differs")
        check(n == len(rec), f"scripts: {n} regenerated, {len(rec)} recorded")
        scripts = f"{n} regenerated, SHA-256 compared"
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
    inv = f"(invoke {lean_str(a['field'])} {' '.join(wast_val(show_val(v)) for v in a['args'])})"
    if r["type"] == "assert_trap":
        return f"(assert_trap {inv} {lean_str(r.get('text', ''))})"
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
