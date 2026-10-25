module

public import Silmaril.Wasm.V1.Modules
public import Silmaril.Wasm.Wat.Print.Common

/-! # WebAssembly 1.0 module WAT printer

`printV1Module : V1.Module → String` renders a source-level WebAssembly 1.0 module
(`Silmaril.Wasm.V1.Module`, the W3C Recommendation of 5 December 2019,
https://www.w3.org/TR/2019/REC-wasm-core-1-20191205/) as standard WebAssembly text
(core specification, chapter "Text Format"; pinned in `specs/wasm/core-3.0.json` at
WebAssembly/spec 608711107b7f1edb13efd57b7d79b49477462d36, sources
`specification/wasm-3.0/6.3-text.instructions.spectec` and `6.4-text.modules.spectec`).
All numbers, floats, strings, names, types and memory arguments are printed by the shared primitives
of `Silmaril.Wasm.Wat.Print.Common`.

Printed form (index references only; identifiers `$x` are never printed):
* `(module` followed by one field (or field line group) per line, indented by two
  spaces, in the order types, imports, funcs, tables, memories, globals, exports, start,
  elems, data (the text format requires imports before definitions; within each index
  space the order of appearance is the AST order, so every printed index denotes the
  same entity), the closing `)` appended to the last line; the empty module prints as
  `(module)`;
* `(type (func (param …) (result …)))` via `funcTypeText`;
* `(import "mod" "name" desc)` with `desc` one of `(func (type N))`,
  `(table min max? funcref)`, `(memory min max?)`, `(global t)` / `(global (mut t))`;
* `(func (type N) (local t…)` then the body, one flat instruction per line indented
  one level deeper than the `(func` line, with the closing `)` appended to the last
  line; nested bodies of `block`/`loop`/`if` are indented one further level and closed
  by `end` (and `else`) on their own lines at the level of the opening keyword; an empty
  `else` arm is omitted; block types print as nothing or `(result t)`;
* `(table min max? funcref)`, `(memory min max?)`, `(global gt instr…)`: a constant
  expression is printed on one line by `exprInline`, as its unindented instruction lines
  joined by single spaces (a nested body adds no extra spacing:
  `block (result i32) i32.const 0 end`); constant expressions of valid modules never
  contain blocks, so this only fixes the layout of (invalid) inputs that do;
* `(export "name" (func|table|memory|global N))`, `(start N)`;
* `(elem (table N)? (offset instr…) func i…)` and
  `(data (memory N)? (offset instr…) "bytes")`, with `(table 0)` / `(memory 0)` left
  implicit (the text format defaults an omitted table/memory use to 0);
* instruction mnemonics as in the specification: `iN.load8_s`, `i64.store32`,
  `i32.wrap_i64`, `f64.convert_i32_u`, `i32.reinterpret_f32`, …; `call_indirect (type N)`;
  integer constants print the unsigned decimal value of the bit pattern and float
  constants print exactly from their bit patterns (`nan:0x…` payloads included);
  memory arguments print `offset=N` / `align=M` only when not default, where the natural
  alignment is the access width (packed width for packed accesses).

Every constructor of `V1.Instr`, `V1.ImportDesc`, `V1.ExternIdx`, `V1.ConvertOp`,
`V1.IntUnOp` and of the shared operator families has its own printing case (no
catch-all). Representable but invalid instructions (e.g. `i32` with a 32-bit packed
load) are printed mechanically (`i32.load32_s`); validity is the concern of
`V1.Validation`, and only valid modules are intended to produce parseable text.

Relation to the Lime1 printer (`Silmaril/Wasm/Wat/Print/Lime1.lean`): this file
does not depend on it, but uses the same layout, so that on every module
`printV1Module m = printLime1Module m.toLime` (theorem `printV1Module_eq_toLime` in
`Silmaril/Wasm/Wat/Print/V1/Examples.lean`); there are no documented differences.

Not modelled / not claimed: no parser round-trip theorem (`Silmaril/Wasm/Wat` is an
elaboration-time `meta` parser, not an executable one); acceptance by
`wasm-tools parse` is checked by the external harness, not proved here. No
names/custom sections are emitted.
-/

@[expose] public section

namespace Silmaril.Wasm.Wat.Print

/-! Helpers of the V1 printer live in `V1Text`, to avoid clashes with the helpers of the
Lime1 printer, which live in `Lime1Text`. -/

namespace V1Text

open Silmaril.Wasm.V1 (Instr Expr ImportDesc Import ExternIdx Export)

/-! ## Small helpers -/

/-- Decimal text of an index. -/
def idx {k : IndexKind} (i : Idx k) : String := nat i.value.val

/-- Append `)` to the last line (no-op on the empty list). -/
def closeLast : List String → List String
  | [] => []
  | [l] => [l ++ ")"]
  | l :: ls => l :: closeLast ls

/-- `i32` / `i64`. -/
def intType : IntType → String
  | .i32 => "i32"
  | .i64 => "i64"

/-- `f32` / `f64`. -/
def floatType : FloatType → String
  | .f32 => "f32"
  | .f64 => "f64"

/-- Signedness suffix `_s` / `_u`. -/
def sign : Signedness → String
  | .signed => "_s"
  | .unsigned => "_u"

/-- Limits `min max?`. -/
def limits (l : V1.Limits) : String :=
  spaced [nat l.min.val, match l.max with | some m => nat m.val | none => ""]

/-- Table type `min max? funcref` (1.0 tables always hold `funcref`). -/
def tableType (t : V1.TableType) : String := spaced [limits t.limits, "funcref"]

/-- Memory type `min max?`. -/
def memoryType (t : V1.MemoryType) : String := limits t.limits

/-- Global type `t` or `(mut t)`. -/
def globalType (t : V1.GlobalType) : String :=
  match t.mutability with
  | .const => v1ValType t.value
  | .var => sexp "mut" [v1ValType t.value]

/-- Block type: empty or `(result t)`. -/
def blockType : V1.BlockType → String
  | none => ""
  | some t => sexp "result" [v1ValType t]

/-! ## Operators -/

def intUnOp : V1.IntUnOp → String
  | .clz => "clz"
  | .ctz => "ctz"
  | .popcnt => "popcnt"

def intBinOp : IntBinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div s => "div" ++ sign s
  | .rem s => "rem" ++ sign s
  | .and => "and"
  | .or => "or"
  | .xor => "xor"
  | .shl => "shl"
  | .shr s => "shr" ++ sign s
  | .rotl => "rotl"
  | .rotr => "rotr"

def intTestOp : IntTestOp → String
  | .eqz => "eqz"

def intRelOp : IntRelOp → String
  | .eq => "eq"
  | .ne => "ne"
  | .lt s => "lt" ++ sign s
  | .gt s => "gt" ++ sign s
  | .le s => "le" ++ sign s
  | .ge s => "ge" ++ sign s

def floatUnOp : FloatUnOp → String
  | .abs => "abs"
  | .neg => "neg"
  | .sqrt => "sqrt"
  | .ceil => "ceil"
  | .floor => "floor"
  | .trunc => "trunc"
  | .nearest => "nearest"

def floatBinOp : FloatBinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .min => "min"
  | .max => "max"
  | .copysign => "copysign"

def floatRelOp : FloatRelOp → String
  | .eq => "eq"
  | .ne => "ne"
  | .lt => "lt"
  | .gt => "gt"
  | .le => "le"
  | .ge => "ge"

/-- Full mnemonic of a 1.0 conversion (`target.op_source_sx`). -/
def convertOp : V1.ConvertOp → String
  | .wrap => "i32.wrap_i64"
  | .extend s => "i64.extend_i32" ++ sign s
  | .trunc src tgt s => intType tgt ++ ".trunc_" ++ floatType src ++ sign s
  | .convert src tgt s => floatType tgt ++ ".convert_" ++ intType src ++ sign s
  | .demote => "f32.demote_f64"
  | .promote => "f64.promote_f32"
  | .reinterpretInt .f32 => "i32.reinterpret_f32"
  | .reinterpretInt .f64 => "i64.reinterpret_f64"
  | .reinterpretFloat .i32 => "f32.reinterpret_i32"
  | .reinterpretFloat .i64 => "f64.reinterpret_i64"

/-! ## Memory accesses and constants -/

/-- Width suffix of a packed access. -/
def packWidth : V1.PackSize → String
  | .i8 => "8"
  | .i16 => "16"
  | .i32 => "32"

/-- log2 of the byte width of a packed access (its natural alignment). -/
def packAlign : V1.PackSize → Nat
  | .i8 => 0
  | .i16 => 1
  | .i32 => 2

/-- log2 of the byte width of an unpacked integer access. -/
def intAlign : IntType → Nat
  | .i32 => 2
  | .i64 => 3

/-- log2 of the byte width of a float access. -/
def floatAlign : FloatType → Nat
  | .f32 => 2
  | .f64 => 3

/-- `op` followed by its non-default memory argument fields (if any). -/
def withMemarg (op : String) (a : V1.MemArg) (natural : Nat) : String :=
  spaced [op, memarg a.offset.val a.align.val natural]

/-- Exact text of a float constant's bits (`f32Bits` / `f64Bits`). -/
def floatConst : (t : FloatType) → BitVec t.width → String
  | .f32, b => floatBits 8 23 b.toNat
  | .f64, b => floatBits 11 52 b.toNat

/-! ## Instructions -/

mutual
/-- Lines of one instruction, where `nest` lays out the lines of a nested body
(`indent 1` for multi-line bodies, `id` for one-line expressions); structured
instructions span several lines. Every constructor has its own case. -/
def instrLinesWith (nest : List String → List String) : Instr → List String
  | .nop => ["nop"]
  | .unreachable => ["unreachable"]
  | .drop => ["drop"]
  | .select => ["select"]
  | .block t body => spaced ["block", blockType t] :: nest (exprLinesWith nest body) ++ ["end"]
  | .loop t body => spaced ["loop", blockType t] :: nest (exprLinesWith nest body) ++ ["end"]
  | .if_ t thenBody elseBody =>
    let elseLines := match elseBody with
      | [] => []
      | _ :: _ => "else" :: nest (exprLinesWith nest elseBody)
    spaced ["if", blockType t] :: nest (exprLinesWith nest thenBody) ++ elseLines ++ ["end"]
  | .br l => ["br " ++ idx l]
  | .brIf l => ["br_if " ++ idx l]
  | .brTable ls l => [spaced ("br_table" :: ls.map idx ++ [idx l])]
  | .call f => ["call " ++ idx f]
  | .callIndirect t => ["call_indirect " ++ sexp "type" [idx t]]
  | .return_ => ["return"]
  | .localGet x => ["local.get " ++ idx x]
  | .localSet x => ["local.set " ++ idx x]
  | .localTee x => ["local.tee " ++ idx x]
  | .globalGet x => ["global.get " ++ idx x]
  | .globalSet x => ["global.set " ++ idx x]
  | .intLoad t none a => [withMemarg (intType t ++ ".load") a (intAlign t)]
  | .intLoad t (some (n, s)) a =>
    [withMemarg (intType t ++ ".load" ++ packWidth n ++ sign s) a (packAlign n)]
  | .floatLoad t a => [withMemarg (floatType t ++ ".load") a (floatAlign t)]
  | .intStore t none a => [withMemarg (intType t ++ ".store") a (intAlign t)]
  | .intStore t (some n) a =>
    [withMemarg (intType t ++ ".store" ++ packWidth n) a (packAlign n)]
  | .floatStore t a => [withMemarg (floatType t ++ ".store") a (floatAlign t)]
  | .memorySize => ["memory.size"]
  | .memoryGrow => ["memory.grow"]
  | .intConst t b => [intType t ++ ".const " ++ bitsConst b]
  | .floatConst t b => [floatType t ++ ".const " ++ floatConst t b]
  | .intUnOp t op => [intType t ++ "." ++ intUnOp op]
  | .intBinOp t op => [intType t ++ "." ++ intBinOp op]
  | .intTestOp t op => [intType t ++ "." ++ intTestOp op]
  | .intRelOp t op => [intType t ++ "." ++ intRelOp op]
  | .floatUnOp t op => [floatType t ++ "." ++ floatUnOp op]
  | .floatBinOp t op => [floatType t ++ "." ++ floatBinOp op]
  | .floatRelOp t op => [floatType t ++ "." ++ floatRelOp op]
  | .convert op => [convertOp op]

/-- Lines of an instruction sequence (nested bodies laid out by `nest`). -/
def exprLinesWith (nest : List String → List String) : Expr → List String
  | [] => []
  | i :: is => instrLinesWith nest i ++ exprLinesWith nest is
end

/-- Lines of one instruction, nested bodies indented by one level. -/
def instrLines (i : Instr) : List String := instrLinesWith (indent 1) i

/-- Lines of an instruction sequence, nested bodies indented by one level. -/
def exprLines (e : Expr) : List String := exprLinesWith (indent 1) e

/-- An instruction sequence on one line (global initializers and segment offsets): the
lines of the unindented layout joined by single spaces, so a nested `block … end` adds no
extra spaces. -/
def exprInline (e : Expr) : String := spaced (exprLinesWith id e)

/-! ## Module fields -/

/-- `(type (func …))`. -/
def typeField (t : V1.FuncType) : List String := [sexp "type" [funcTypeText t]]

/-- Import descriptor `(func (type N))`, `(table …)`, `(memory …)`, `(global …)`. -/
def importDesc : ImportDesc → String
  | .func t => sexp "func" [sexp "type" [idx t]]
  | .table t => sexp "table" [tableType t]
  | .memory t => sexp "memory" [memoryType t]
  | .global t => sexp "global" [globalType t]

/-- `(import "m" "n" desc)`. -/
def importField (i : Import) : List String :=
  [sexp "import" [name i.moduleName, name i.name, importDesc i.desc]]

/-- `(func (type N) (local …)` then the indented body, closed on its last line. -/
def funcField (f : V1.Func) : List String :=
  let locals := match f.locals with
    | [] => ""
    | ls => sexp "local" (ls.map v1ValType)
  closeLast (spaced ["(func", sexp "type" [idx f.type], locals] :: indent 1 (exprLines f.body))

/-- `(table min max? funcref)`. -/
def tableField (t : V1.TableType) : List String := [sexp "table" [tableType t]]

/-- `(memory min max?)`. -/
def memoryField (t : V1.MemoryType) : List String := [sexp "memory" [memoryType t]]

/-- `(global type init…)`. -/
def globalField (g : V1.Global) : List String :=
  [sexp "global" [globalType g.type, exprInline g.init]]

/-- Export descriptor `(func N)` etc. -/
def externIdx : ExternIdx → String
  | .func i => sexp "func" [idx i]
  | .table i => sexp "table" [idx i]
  | .memory i => sexp "memory" [idx i]
  | .global i => sexp "global" [idx i]

/-- `(export "n" desc)`. -/
def exportField (e : Export) : List String := [sexp "export" [name e.name, externIdx e.index]]

/-- `(start N)` if present. -/
def startField : Option FuncIdx → List String
  | none => []
  | some f => [sexp "start" [idx f]]

/-- `(elem (table N)? (offset …) func i*)`; `(table 0)` is left implicit. -/
def elemField (e : V1.Elem) : List String :=
  let table := if e.table.value.val = 0 then "" else sexp "table" [idx e.table]
  [sexp "elem" ([table, sexp "offset" [exprInline e.offset], "func"] ++ e.init.map idx)]

/-- `(data (memory N)? (offset …) "bytes")`; `(memory 0)` is left implicit. -/
def dataField (d : V1.Data) : List String :=
  let mem := if d.memory.value.val = 0 then "" else sexp "memory" [idx d.memory]
  [sexp "data" [mem, sexp "offset" [exprInline d.offset], string d.bytes.data.toList]]

/-- All module field lines, in text order (imports before definitions). -/
def moduleFieldLines (m : V1.Module) : List String :=
  m.types.flatMap typeField ++ m.imports.flatMap importField ++ m.funcs.flatMap funcField ++
    m.tables.flatMap tableField ++ m.memories.flatMap memoryField ++
    m.globals.flatMap globalField ++ m.exports.flatMap exportField ++ startField m.start ++
    m.elems.flatMap elemField ++ m.data.flatMap dataField

end V1Text

/-- Standard WebAssembly text of a 1.0 module (layout in the module docstring). The empty
module prints as `(module)`. -/
def printV1Module (m : Silmaril.Wasm.V1.Module) : String :=
  lines (V1Text.closeLast ("(module" :: indent 1 (V1Text.moduleFieldLines m)))

/-- WebAssembly text of a 1.0 instruction sequence, one instruction per line (nested
bodies indented by two spaces per level). -/
def printV1Expr (e : Silmaril.Wasm.V1.Expr) : String := lines (V1Text.exprLines e)

theorem printV1Module_empty : printV1Module {} = "(module)" := by decide +kernel

end Silmaril.Wasm.Wat.Print
