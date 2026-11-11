"""Regenerate Silmaril/Wasm/Tools/WastEnc/Ops/Defs.lean: every instruction of the `wast` crate's
`instructions!` table (`crates/wast/src/core/expr.rs`) with its text name, the kind of its
immediate (the Rust payload type, plus the index space for `Index` payloads, from
`crates/wast/src/core/resolve/names.rs`) and its opcode prefix (the leading
`self.sink.push(0x..)` / `0x..u32.encode(self.sink)` statements of the `InstructionSink`
method of the same name in `crates/wasm-encoder/src/core/instructions.rs`), from the
wasm-tools 1.262.0 source archive.

  python3 -I tools/wasm-tools/tests/gen-ops.py SRC_DIR OUT.lean
"""
import re, sys

src, out = sys.argv[1], sys.argv[2]
expr = open(f"{src}/crates/wast/src/core/expr.rs").read()
sink = open(f"{src}/crates/wasm-encoder/src/core/instructions.rs").read()

body = expr[expr.index("instructions! {\n    pub enum Instruction"):]
body = body[: body.index("\n}\n")]
rows = []
custom = False
for line in body.splitlines():
    s = line.strip()
    if s == "#[custom_encode]":
        custom = True
        continue
    m = re.match(r'^([a-z_0-9]+)(?:\((.*)\))?\s*:\s*"([^"]+)"(?:\s*\|\s*"([^"]+)")?,$', s)
    if not m:
        continue
    rows.append((m.group(1), m.group(2) or "", m.group(3), m.group(4), custom))
    custom = False

# Index spaces of `Index` payloads (names.rs `resolve_instr`).
NS = {
    "br": "label", "br_if": "label", "br_on_null": "label", "br_on_non_null": "label",
    "rethrow": "label", "delegate": "label",
    "call": "func", "return_call": "func", "ref_func": "func",
    "call_ref": "type", "return_call_ref": "type",
    "local_get": "local", "local_set": "local", "local_tee": "local",
    "global_get": "global", "global_set": "global",
    "data_drop": "data", "elem_drop": "elem",
    "throw": "tag", "catch": "tag", "suspend": "tag",
    "cont_new": "type",
    "struct_new_desc": "type", "struct_new_default_desc": "type", "ref_get_desc": "type",
}
for n in ["struct_new", "struct_new_default", "array_new", "array_new_default", "array_get",
          "array_get_s", "array_get_u", "array_set"]:
    NS[n] = "type"


def kind(name, arg):
    a = arg.replace("<'a>", "").replace("Box<", "").replace(">", "")
    if arg == "":
        return ".none"
    if a == "Index":
        return f".idx .{NS[name]}"
    if a == "Ordered<Index" or arg == "Ordered<Index<'a>>":
        return ".ordIdx ." + ("global" if name.startswith("global") else "type")
    m = re.match(r"MemArg<(\d+)", arg)
    if m:
        return f".memarg {m.group(1)}"
    m = re.match(r"LoadOrStoreLane<(\d+)", arg)
    if m:
        return f".lsLane {m.group(1)}"
    simple = {
        "LaneArg": ".lane", "StructAccess": ".struct", "Ordered<StructAccess": ".ordStruct",
        "TableArg": ".table", "Ordered<TableArg": ".ordTable", "MemoryArg": ".memory",
        "BlockType": ".block", "Option<Id": ".endLabel", "CallIndirect": ".callIndirect",
        "V128Const": ".v128", "TryTable": ".tryTable", "TableInit": ".tableInit",
        "TableCopy": ".tableCopy", "Switch": ".switch", "SelectTypes": ".select",
        "ResumeThrowRef": ".resumeThrowRef", "ResumeThrow": ".resumeThrow", "Resume": ".resume",
        "RefTest": ".refTest", "RefCast": ".refCast", "RefCastDescEq": ".refCastDescEq",
        "MemoryInit": ".memoryInit", "MemoryCopy": ".memoryCopy", "I8x16Shuffle": ".shuffle",
        "i64": ".i64", "i32": ".i32", "HeapType": ".heap", "F64": ".f64", "F32": ".f32",
        "ContBind": ".contBind", "BrTableIndices": ".brTable", "BrOnCast": ".brOnCast",
        "BrOnCastFail": ".brOnCastFail", "BrOnCastDescEq": ".brOnCastDescEq",
        "BrOnCastDescEqFail": ".brOnCastDescEqFail", "ArrayNewFixed": ".arrayNewFixed",
        "ArrayNewElem": ".arrayNewElem", "ArrayNewData": ".arrayNewData", "ArrayFill": ".arrayFill",
        "ArrayCopy": ".arrayCopy",
    }
    if a in simple:
        return simple[a]
    if a == "ArrayInit":
        return ".arrayInit ." + ("data" if name.endswith("data") else "elem")
    raise SystemExit(f"unknown payload {arg!r} of {name}")


def prefix(method):
    m = re.search(r"pub fn " + method + r"\b[^{]*\{\n(.*?)\n    \}", sink, re.S)
    if not m:
        return None
    out = []
    for st in m.group(1).splitlines():
        st = st.strip()
        p = re.match(r"self\.sink\.push\((0x[0-9A-Fa-f]+)\);", st)
        u = re.match(r"(0x[0-9A-Fa-f]+|[0-9]+)u32\.encode\(self\.sink\);", st)
        if p:
            out.append(int(p.group(1), 16))
        elif u:
            v = int(u.group(1), 0)
            while True:
                b = v & 0x7F
                v >>= 7
                if v:
                    out.append(b | 0x80)
                else:
                    out.append(b)
                    break
        else:
            break
    return out


# Instructions whose payload selects among several sink methods (custom encoders): the
# prefix of the method used by each variant; the IO layer of this table never sees them
# without a payload.
CUSTOM_METHODS = {
    "select": "select", "br_table": "br_table", "call_indirect": "call_indirect",
    "return_call_indirect": "return_call_indirect", "ref_test": "ref_test_nullable",
    "ref_cast": "ref_cast_nullable", "ref_cast_desc_eq": "ref_cast_desc_eq_nullable",
}

lines_out = []
missing = []
for (name, arg, text, dep, cust) in rows:
    k = kind(name, arg)
    method = {"if_": "if_", "loop_": "loop_", "else_": "else_", "return_": "return_",
              "try_": "try_"}.get(name, name)
    method = CUSTOM_METHODS.get(name, method)
    p = prefix(method)
    if p is None:
        missing.append(name)
        p = []
    bs = ", ".join(f"0x{b:02x}" for b in p)
    lines_out.append(f'  ⟨"{text}", [{bs}], {k}⟩,')
    if dep:
        lines_out.append(f'  ⟨"{dep}", [{bs}], {k}⟩,')
lines_out[-1] = lines_out[-1].rstrip(",")

hdr = [
    "module", "",
    "/-! The instructions of the `wast` crate (wasm-tools 1.262.0): text name, opcode prefix and",
    "immediate kind, generated by `tools/wasm-tools/tests/gen-ops.py` from",
    "`crates/wast/src/core/expr.rs` (`instructions!`), `crates/wast/src/core/resolve/names.rs`",
    "(index spaces) and `crates/wasm-encoder/src/core/instructions.rs` (opcodes); do not edit. -/",
    "", "@[expose] public section", "",
    "namespace Silmaril.Wasm.Tools.WastEnc", "",
    "/-- The index spaces of the text format (`Ns` of `resolve/mod.rs`, plus locals, labels, data",
    "and element segments). -/",
    "inductive Space where",
    "  | func | table | memory | global | tag | type | data | elem | local | label",
    "  deriving DecidableEq, Repr, Inhabited", "",
    "/-- The payload kinds of `instructions!` (the Rust payload type; for `Index`, its space). -/",
    "inductive ImmKind where",
    "  | none | idx (s : Space) | ordIdx (s : Space) | memarg (align : Nat) | lsLane (align : Nat)",
    "  | lane | struct | ordStruct | table | ordTable | memory | block | endLabel | callIndirect",
    "  | v128 | tryTable | tableInit | tableCopy | switch | select | resumeThrowRef | resumeThrow",
    "  | resume | refTest | refCast | refCastDescEq | memoryInit | memoryCopy | shuffle | i64 | i32",
    "  | heap | f64 | f32 | contBind | brTable | brOnCast | brOnCastFail | brOnCastDescEq",
    "  | brOnCastDescEqFail | arrayNewFixed | arrayNewElem | arrayNewData | arrayFill | arrayCopy",
    "  | arrayInit (s : Space)",
    "  deriving DecidableEq, Repr, Inhabited", "",
    "/-- One row of the table: text name, opcode prefix, payload kind. -/",
    "structure OpRow where",
    "  name : String",
    "  code : List UInt8",
    "  kind : ImmKind",
    "  deriving Repr, Inhabited", "",
    "/-- Every instruction of `instructions!`, in its order. -/",
    "def ops : List OpRow := [",
]
tail = ["]", "", "end Silmaril.Wasm.Tools.WastEnc", ""]
open(out, "w").write("\n".join(hdr + lines_out + tail))
print(len(rows), "instructions; no sink method for:", missing)
