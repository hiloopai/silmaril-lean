#!/usr/bin/env python3
"""Generate the `decode?` certificates of the core modules of the four WASI 0.3 examples.

For each core module `CoreI` of `X` (`Silmaril.Project.WasmP3Rust.X.CoreI`, written by Certs.lean),
writes
  Silmaril/Project/WasmP3Rust/X/CoreI/Locals/Thms.lean  (chkLocals of each code group), and
  Silmaril/Project/WasmP3Rust/X/CoreI/Decode/Thms.lean  (`decode_eq : decode? (arr (slice bytes A Z))
                                                       = some module`),
from the section layout of the binary (read here) and the checker expressions of
`CoreI/Defs.lean` and `CoreI/Code/Gk/Defs.lean`. Usage (from the repository root):
  python3 examples/wasip3-rust/gen/decode_certs.py
The binaries are only parsed for their section framing (ids, LEB128 sizes); nothing is executed.
"""
import os, re, sys

ROOT = os.getcwd()
FILES = {"Hello": "hello.wasm", "Cat": "cat.wasm", "Echo": "echo.wasm", "CatDebug": "cat-debug.wasm"}
VEC = {  # id: (field, reader, frame, mono, body)
    1: ("types", "readRecType", "frame_readRecType", "mono_readRecType", "body_types"),
    2: ("imports", "readImport", "frame_readImport", "mono_readImport", "body_imports"),
    3: ("funcTypes", "readIdx", "(frame_readIdx (k := .type_))", "(mono_readIdx (k := .type_))", "body_funcs"),
    4: ("tables", "readTable", "frame_readTable", "mono_readTable", "body_tables"),
    5: ("memories", "readMemType", "frame_readMemType", "mono_readMemType", "body_mems"),
    6: ("globals", "readGlobal", "frame_readGlobal", "mono_readGlobal", "body_globals"),
    7: ("exports", "readExport", "frame_readExport", "mono_readExport", "body_exports"),
    9: ("elems", "readElem", "frame_readElem", "mono_readElem", "body_elems"),
    13: ("tags", "readTag", "frame_readTag", "mono_readTag", "body_tags"),
}

def leb(b, p):
    v, s, n = 0, 0, 0
    while True:
        x = b[p + n]; n += 1
        v |= (x & 0x7F) << s; s += 7
        if x < 0x80:
            return v, n

def ranges(name):
    """The core module slices of the component, from P3/Defs.lean."""
    src = open(f"{ROOT}/Silmaril/Project/WasmP3Rust/{name}/P3/Defs.lean").read()
    rs = [(int(a), int(z)) for a, z in re.findall(r"coreModule \(arr \(slice bytes (\d+) (\d+)\)\)", src)]
    if not rs:
        src = open(f"{ROOT}/Silmaril/Project/WasmP3Rust/HelloP3/Defs.lean").read()
        rs = [(int(a), int(z)) for a, z in re.findall(r"coreModule \(arr \(slice Hello\.File\.bytes (\d+) (\d+)\)\)", src)]
    return rs

def defs_exprs(path):
    src = open(path).read()
    out = {}
    for field, expr in re.findall(r"noncomputable def (\w+) := \((chkSection .*)\)\.getD \[\]\n", src):
        out[field] = expr
    m = re.search(r"noncomputable def datas : List Silmaril\.Wasm\.Data :=\s*\((chkSection .*)\)\.getD \[\]\n", src)
    if m:
        out["datas"] = m.group(1)
    m = re.search(r"\[(Code\.G\d+\.codes(?:, Code\.G\d+\.codes)*)\]\.flatten", src)
    groups = re.findall(r"Code\.G(\d+)\.codes", m.group(1)) if m else []
    return out, [int(g) for g in groups]

def group_slice(path):
    src = open(path).read()
    a, z = re.search(r"codesOf plans \(slice bytes (\d+) (\d+)\)", src).groups()
    return int(a), int(z)

def gen(name, idx, A, Z, b):
    base = f"{ROOT}/Silmaril/Project/WasmP3Rust/{name}/Core{idx}"
    ns = f"Silmaril.Project.WasmP3Rust.{name}.Core{idx}"
    exprs, groups = defs_exprs(f"{base}/Defs.lean")
    gsl = {g: group_slice(f"{base}/Code/G{g}/Defs.lean") for g in groups}
    p = A + 8
    haves, steps, facts, dfacts = [], [], [], []
    last = 0
    while p < Z:
        sid = b[p]
        size, k = leb(b, p + 1)
        x = p + 1 + k
        e = x + size
        if sid == 0:
            nlen, nk = leb(b, x)
            y = x + nk + nlen
            nm = b[x + nk:y].decode("utf-8")
            steps.append(f"go_custom_parts (L := bytes) (A := {A}) (Z := {Z}) (s := {p}) (x := {x}) (y := {y}) (e := {e}) (nm := {nm!r}.replace(\"'\", '\"')) W W W rfl (by decide) (by decide) (by decide) (by decide) (by decide) hL".replace("{nm!r}", ""))
            steps[-1] = (f"go_custom_parts (L := bytes) (A := {A}) (Z := {Z}) (s := {p}) (x := {x}) (y := {y}) "
                         f"(e := {e}) (nm := \"{nm}\") W W W rfl (by decide) (by decide) (by decide) (by decide) "
                         f"(by decide) hL")
        elif sid == 10:
            cnt, ck = leb(b, x)
            z = x + ck
            segs = [f"codes_seg_s (L := bytes) (A := {A}) (Z := {Z}) Code.G{g}.ok localsG{g} (by decide) (by decide) (by decide) hL" for g in groups]
            # chain the groups
            seg = segs[-1]
            for s_ in reversed(segs[:-1]):
                seg = f"(({s_}).append ({seg}))"
            assert gsl[groups[0]][0] == z and gsl[groups[-1]][1] == e, (name, idx, gsl, z, e)
            haves.append(f"theorem codes_length' : codes.length = {cnt} :=\n  (length_flatten_of ({' '.join('(.cons Code.G%d.length' % g for g in groups)} .nil{')' * len(groups)})).trans (by decide)")
            haves.append(f"theorem codes_seg : VecSeg readCode (slice bytes {A} {Z}) ({z} - {A}) ({e} - {A}) codes := by\n  have := {seg.replace('hL', 'le_length')}\n  simpa only [codes, {', '.join('Code.G%d.codes' % g for g in groups)}, List.flatten_cons, List.flatten_nil, List.append_nil] using this")
            steps.append(f"go_code_s (L := bytes) (A := {A}) (Z := {Z}) (s := {p}) (x := {x}) (z := {z}) (e := {e}) (len := {size}) W W rfl (by rw [codes_length']; simp only [bytes, slice_decode]; decide +kernel) codes_seg (by decide) (by decide) (by decide) (by decide) (by decide) hL (by rw [codes_length']; decide) (by decide)")
            last = 12
            continue_ = True
        elif sid == 11:
            expr = exprs["datas"]
            assert f"(slice bytes {p} {e})" in expr, (name, idx, expr, p, e)
            dfacts.append(f"theorem sec{p} : {expr} = some datas :=\n  getD_of_isSome [] (by simp only [bytes, slice_decode]; decide +kernel)")
            steps.append(f"go_data_s (L := bytes) (A := {A}) (Z := {Z}) sec{p} (by decide) (by decide) (by decide) hL (by decide)")
        elif sid in VEC:
            field, reader, fr, mo, body = VEC[sid]
            expr = exprs[field]
            assert f"(slice bytes {p} {e})" in expr, (name, idx, field, expr, p, e)
            facts.append(f"theorem sec{p} : {expr} = some {field} :=\n  getD_of_isSome [] (by simp only [bytes, slice_decode]; decide +kernel)")
            steps.append(f"go_vec_s (L := bytes) (A := {A}) (Z := {Z}) (N := {sid}) {fr} {mo} {body} sec{p} (by decide) (by decide) (by decide) hL (by decide) (by decide)")
        else:
            sys.exit(f"{name} Core{idx}: section {sid} not handled")
        p = e
    assert p == Z
    W = "(by simp only [bytes, slice_decode]; decide +kernel)"
    steps = [re.sub(r"\bW\b", W, s) for s in steps]
    steps = [st.replace(" hL", " le_length") for st in steps]
    chain = "".join(f"\n    (({st}).trans" for st in steps)
    close = ")" * len(steps)
    has_code = bool(groups)
    plain = "".join(", " + n for n in re.findall(r"^def (\w+) :=", open(f"{base}/Defs.lean").read(), re.M))
    imports = [f"public import {ns}.Thms", "public import Silmaril.Wasm.Component.ChunkedDecode.Thms",
               f"public import {ns}.Decode.Facts.Thms"]
    if has_code:
        imports.append(f"public import {ns}.Locals.Thms")
    hf = "funcs_length"
    hdi = "dataIdxs"
    out = f"""module

{chr(10).join(imports)}

/-!
# `{name}`, core module {idx}: `decode?` itself

**PROVED**: silmaril's decoder returns `module` on the bytes {A} to {Z} of the file
(`decode_eq`), from the section checks (re-run here), the code group checks
(`Code.Gk.ok`) and the locals checks (`Locals`), through
`Silmaril.Wasm.Component.ChunkedDecode.decode_s`.

GENERATED by `python3 examples/wasip3-rust/gen/decode_certs.py`; do not edit.
-/

@[expose] public section

-- Generated proofs share one simp set; some of its lemmas are unused in some files.
set_option linter.unusedSimpArgs false

namespace {ns}
open Silmaril.Wasm.Component.Chunked Silmaril.Wasm.Component.ChunkedDecode
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core Silmaril.Wasm.Binary.Core.Decode
open {'Silmaril.Project.WasmP3Rust.' + name}.File

set_option maxRecDepth 100000

theorem le_length : {Z} ≤ bytes.length := by rw [bytes_length]; decide

{(chr(10) + chr(10)).join(haves)}

/-- **Core module {idx} decodes to `module`** under silmaril's `decode?`. -/
theorem decode_eq : decode? (arr (slice bytes {A} {Z})) = some module :=
  (decode_s (L := bytes) (A := {A}) (Z := {Z}) header (by decide) le_length
    (show readModule.go ({Z} - {A}) 0 {{}} ⟨arr (slice bytes {A} {Z}), {A} + 8 - {A}⟩ = _ from{chain}
      (go_end_s (L := bytes) (A := {A}) (Z := {Z}) (by decide) le_length){close})
    (by dsimp only; exact {hf}) (by rfl) (by dsimp only; exact {hdi})).trans
    (by dsimp only [module{plain}])

end {ns}

end
"""
    os.makedirs(f"{base}/Decode", exist_ok=True)
    open(f"{base}/Decode/Thms.lean", "w").write(out)
    fout = f"""module

public import {ns}.Defs
public import Silmaril.Wasm.Component.Chunked.Thms

/-!
# `{name}`, core module {idx}: the section checks, as equations

**PROVED** (kernel checks of the plans on windows of the file): each vector section's checker
returns its value (the facts `Sections/Thms` uses through `isSome`), for `Decode/Thms`.

GENERATED by `python3 examples/wasip3-rust/gen/decode_certs.py`; do not edit.
-/

@[expose] public section

namespace {ns}
open Silmaril.Wasm.Component.Chunked
open Silmaril.Wasm.Binary.Core.Decode
open {'Silmaril.Project.WasmP3Rust.' + name}.File

set_option maxRecDepth 100000

{(chr(10) + chr(10)).join(facts)}

end {ns}

end
"""
    os.makedirs(f"{base}/Decode/Facts", exist_ok=True)
    if dfacts:
        os.makedirs(f"{base}/Decode/Facts/Data", exist_ok=True)
        dout = fout.replace("(chr(10) + chr(10)).join(facts)", "")
        dout = fout.replace("\n\n".join(facts), "\n\n".join(dfacts)).replace(
            "each vector section's checker\nreturns its value", "the data section's checker\nreturns its value")
        open(f"{base}/Decode/Facts/Data/Thms.lean", "w").write(dout)
        fout = fout.replace(f"public import {ns}.Defs\n", f"public import {ns}.Defs\npublic import {ns}.Decode.Facts.Data.Thms\n")
    open(f"{base}/Decode/Facts/Thms.lean", "w").write(fout)
    if has_code:
      chunks = [groups[i:i + 8] for i in range(0, len(groups), 8)]
      for ci, chunk in enumerate(chunks):
        gimports = "\n".join(f"public import {ns}.Code.G{g}.Defs" for g in chunk)
        thms = "\n\n".join(
            f"theorem localsG{g} : chkLocals Code.G{g}.plans (slice bytes {gsl[g][0]} {gsl[g][1]}) = true :=\n"
            f"  (by simp only [bytes, slice_decode]; decide +kernel)" for g in chunk)
        lout = f"""module

{gimports}
public import Silmaril.Wasm.Component.ChunkedDecode.Defs
public import Silmaril.Wasm.Component.Chunked.Thms

/-!
# `{name}`, core module {idx}: the locals of each code entry

**PROVED** (kernel): every code entry of each group has at most `maxLocals` locals
(`chkLocals`, which reads only the size and the locals vector of each entry).

GENERATED by `python3 examples/wasip3-rust/gen/decode_certs.py`; do not edit.
-/

@[expose] public section

namespace {ns}
open Silmaril.Wasm.Component.Chunked Silmaril.Wasm.Component.ChunkedDecode
open {'Silmaril.Project.WasmP3Rust.' + name}.File

set_option maxRecDepth 100000

{thms}

end {ns}

end
"""
        os.makedirs(f"{base}/Locals/P{ci}", exist_ok=True)
        open(f"{base}/Locals/P{ci}/Thms.lean", "w").write(lout)
      agg = "\n".join(f"public import {ns}.Locals.P{ci}.Thms" for ci in range(len(chunks)))
      open(f"{base}/Locals/Thms.lean", "w").write(f"""module

{agg}

/-!
# `{name}`, core module {idx}: the locals checks of all code groups

GENERATED by `python3 examples/wasip3-rust/gen/decode_certs.py`; do not edit.
-/
""")
    return f"{ns}.Decode.Thms"

def main():
    only = sys.argv[1:]
    mods = []
    for name, fn in FILES.items():
        if only and name not in only:
            continue
        b = open(f"{ROOT}/examples/wasip3-rust/dist/{fn}", "rb").read()
        for idx, (A, Z) in enumerate(ranges(name)):
            mods.append(gen(name, idx, A, Z, b))
    print("\n".join(mods))

main()
