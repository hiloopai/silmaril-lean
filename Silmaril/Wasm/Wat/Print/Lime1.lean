module

public import Silmaril.Wasm.Wat.Print.Common
public import Silmaril.Wasm.Lime1.Modules

/-! # Lime1 module WAT printer

`printLime1Module : Lime1.Module → String` renders a raw Lime1 module
(`Scalar.Module Lime1.Expr`) as standard WebAssembly text format (core specification,
chapter "Text Format", https://webassembly.github.io/spec/core/text/index.html, pinned in
`specs/wasm/core-3.0.json`), intended to be accepted by `wasm-tools parse`. It is
intended for printing embedded core modules in the component renderer
(`renderLime1Component` in `Silmaril/Wasm/Component/Syntax/Render.lean`).

Produced text:
* one module field per line group, in the order types, imports, funcs, tables,
  memories, globals, exports, start, elem segments, data segments; imports precede all
  definitions, as the text grammar requires, and within each index space the order of
  appearance is the AST order, so every printed index denotes the same entity;
* index references only (no `$` identifiers); functions are `(func (type N) (local …)`
  followed by their body, with parameters taken from the type use;
* function bodies are flat instruction sequences, one instruction per line, with
  `block`/`loop`/`if … else … end` bracketing and two-space indentation per nesting level;
  block types print as nothing, `(result t)` or `(type N)`; an empty `else` arm is
  omitted;
* global initializers and segment offsets are printed on one line by `exprInline`
  (`(global (mut i32) i32.const 0)`, `(offset i32.const 0)`): the unindented instruction
  lines joined by single spaces, so a nested body adds no extra spacing
  (`block (result i32) i32.const 0 end`); constant expressions of valid modules never
  contain blocks, so this only fixes the layout of (invalid) inputs that do;
* element segments on table 0 print `(elem (offset …) func i*)`, others add
  `(table N)`; data segments on memory 0 print `(data (offset …) "…")`, others add
  `(memory N)`; bytes and names use the `\hh`-escaping `string`/`name` of `Wat/Print/Common.lean`;
* integer constants print the unsigned value of their bit pattern, float constants the
  exact hexfloat/`nan:0x…` text of their bits (`bitsConst`, `floatBits`);
* memory arguments print only non-default `offset=`/`align=` fields (`memarg`,
  with the natural alignment of the access).

The helpers live in namespace `Wat.Print.Lime1Text`; only `printLime1Module` and the
shared layout helper `closeLast` are at the root of `Wat.Print`.

Every `Lime1.Instr` constructor (and every operator of `Lime1.IntUnOp`, `IntBinOp`,
`IntTestOp`, `IntRelOp`, `FloatUnOp`, `FloatBinOp`, `FloatRelOp`, `ConvertOp`) has its own
printing case; there is no catch-all.

Not modelled / not claimed: no parser round-trip theorem is proved. The WAT parser in
`Silmaril/Wasm/Wat` is `meta` (elaboration-time) code, so there is no kernel-reducible
parser to state a round trip against; round-tripping through `wasm-tools parse` is checked
by the external harness. The printer does not check validity: invalid modules
(e.g. an `intConst` whose width does not match, out-of-range indices) are printed
verbatim. All functions are total and structurally recursive, so they reduce in the
kernel (see `Wat/Print/Lime1/Examples.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wat.Print

open Silmaril.Wasm

/-- Append `)` to the last line (no-op on the empty list). A generic layout helper, kept
at the root of `Wat.Print` because the component renderer (`Component/Syntax/Render.lean`)
uses it too. -/
def closeLast : List String → List String
  | [] => []
  | [l] => [l ++ ")"]
  | l :: ls => l :: closeLast ls

/-! Every other helper of the Lime1 printer lives in `Lime1Text` (the V1 printer's live in
`V1Text`); only `closeLast` and the entry point `printLime1Module` are at the root of
`Wat.Print`. -/

namespace Lime1Text

/-! ## Small helpers -/

/-- Decimal text of an index. -/
def idx {k : IndexKind} (i : Idx k) : String := nat i.value.val

/-- `i32` / `i64`. -/
def intTypeText : IntType → String
  | .i32 => "i32"
  | .i64 => "i64"

/-- `f32` / `f64`. -/
def floatTypeText : FloatType → String
  | .f32 => "f32"
  | .f64 => "f64"

/-- `_s` / `_u`. -/
def signSuffix : Signedness → String
  | .signed => "_s"
  | .unsigned => "_u"

/-- Bit width text of a packed size (`8`, `16`, `32`). -/
def packText : V1.PackSize → String
  | .i8 => "8"
  | .i16 => "16"
  | .i32 => "32"

/-- log2 of the byte width of a packed access. -/
def packAlignExp : V1.PackSize → Nat
  | .i8 => 0
  | .i16 => 1
  | .i32 => 2

/-- log2 of the byte width of an integer access. -/
def intAlignExp : IntType → Nat
  | .i32 => 2
  | .i64 => 3

/-- log2 of the byte width of a float access. -/
def floatAlignExp : FloatType → Nat
  | .f32 => 2
  | .f64 => 3

/-- `op` followed by its memory argument (non-default fields only). -/
def memInstr (op : String) (arg : Lime1.MemArg) (natural : Nat) : String :=
  spaced [op, memarg arg.offset.val arg.align.val natural]

/-- Limits `min max?`. -/
def limitsText (l : Lime1.Limits) : String :=
  spaced [nat l.min.val, match l.max with | some m => nat m.val | none => ""]

/-- Table type `min max? funcref`. -/
def tableTypeText (t : Lime1.TableType) : String := spaced [limitsText t.limits, "funcref"]

/-- Memory type `min max?`. -/
def memoryTypeText (t : Lime1.MemoryType) : String := limitsText t.limits

/-- Global type `t` or `(mut t)`. -/
def globalTypeText (t : Lime1.GlobalType) : String :=
  match t.mutability with
  | .const => v1ValType t.value
  | .var => sexp "mut" [v1ValType t.value]

/-- Block type: empty, `(result t)` or `(type N)`. -/
def blockTypeText : Lime1.BlockType → String
  | .empty => ""
  | .value t => sexp "result" [v1ValType t]
  | .typeIdx i => sexp "type" [idx i]

/-! ## Operators -/

def intUnOpText : Lime1.IntUnOp → String
  | .clz => "clz"
  | .ctz => "ctz"
  | .popcnt => "popcnt"
  | .extend size => "extend" ++ packText size ++ "_s"

def intBinOpText : IntBinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div s => "div" ++ signSuffix s
  | .rem s => "rem" ++ signSuffix s
  | .and => "and"
  | .or => "or"
  | .xor => "xor"
  | .shl => "shl"
  | .shr s => "shr" ++ signSuffix s
  | .rotl => "rotl"
  | .rotr => "rotr"

def intTestOpText : IntTestOp → String
  | .eqz => "eqz"

def intRelOpText : IntRelOp → String
  | .eq => "eq"
  | .ne => "ne"
  | .lt s => "lt" ++ signSuffix s
  | .gt s => "gt" ++ signSuffix s
  | .le s => "le" ++ signSuffix s
  | .ge s => "ge" ++ signSuffix s

def floatUnOpText : FloatUnOp → String
  | .abs => "abs"
  | .neg => "neg"
  | .sqrt => "sqrt"
  | .ceil => "ceil"
  | .floor => "floor"
  | .trunc => "trunc"
  | .nearest => "nearest"

def floatBinOpText : FloatBinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .min => "min"
  | .max => "max"
  | .copysign => "copysign"

def floatRelOpText : FloatRelOp → String
  | .eq => "eq"
  | .ne => "ne"
  | .lt => "lt"
  | .gt => "gt"
  | .le => "le"
  | .ge => "ge"

/-- Full mnemonic of a conversion (`i32.wrap_i64`, `f64.convert_i32_u`, …). -/
def convertOpText : ConvertOp → String
  | .wrap => "i32.wrap_i64"
  | .extend s => "i64.extend_i32" ++ signSuffix s
  | .trunc src tgt s => intTypeText tgt ++ ".trunc_" ++ floatTypeText src ++ signSuffix s
  | .truncSat src tgt s =>
    intTypeText tgt ++ ".trunc_sat_" ++ floatTypeText src ++ signSuffix s
  | .convert src tgt s =>
    floatTypeText tgt ++ ".convert_" ++ intTypeText src ++ signSuffix s
  | .demote => "f32.demote_f64"
  | .promote => "f64.promote_f32"
  | .reinterpretInt .f32 => "i32.reinterpret_f32"
  | .reinterpretInt .f64 => "i64.reinterpret_f64"
  | .reinterpretFloat .i32 => "f32.reinterpret_i32"
  | .reinterpretFloat .i64 => "f64.reinterpret_i64"

/-- Exact text of a float constant's bits. -/
def floatConstText : (t : FloatType) → BitVec t.width → String
  | .f32, b => floatBits 8 23 b.toNat
  | .f64, b => floatBits 11 52 b.toNat

/-! ## Instructions -/

mutual

/-- Lines of one instruction, where `nest` lays out the lines of a nested body
(`indent 1` for multi-line bodies, `id` for one-line expressions). Structured
instructions span several lines. Every constructor has its own case. -/
def instrLinesWith (nest : List String → List String) : Lime1.Instr → List String
  | .nop => ["nop"]
  | .unreachable => ["unreachable"]
  | .drop => ["drop"]
  | .select => ["select"]
  | .block bt body =>
    spaced ["block", blockTypeText bt] :: nest (exprLinesWith nest body) ++ ["end"]
  | .loop bt body =>
    spaced ["loop", blockTypeText bt] :: nest (exprLinesWith nest body) ++ ["end"]
  | .if_ bt thenBody elseBody =>
    let elseLines := match elseBody with
      | [] => []
      | _ :: _ => "else" :: nest (exprLinesWith nest elseBody)
    spaced ["if", blockTypeText bt] :: nest (exprLinesWith nest thenBody) ++ elseLines ++
      ["end"]
  | .br l => ["br " ++ idx l]
  | .brIf l => ["br_if " ++ idx l]
  | .brTable ls d => [spaced ("br_table" :: ls.map idx ++ [idx d])]
  | .call f => ["call " ++ idx f]
  | .callIndirect t => ["call_indirect " ++ sexp "type" [idx t]]
  | .return_ => ["return"]
  | .localGet i => ["local.get " ++ idx i]
  | .localSet i => ["local.set " ++ idx i]
  | .localTee i => ["local.tee " ++ idx i]
  | .globalGet g => ["global.get " ++ idx g]
  | .globalSet g => ["global.set " ++ idx g]
  | .intLoad t none arg => [memInstr (intTypeText t ++ ".load") arg (intAlignExp t)]
  | .intLoad t (some (p, s)) arg =>
    [memInstr (intTypeText t ++ ".load" ++ packText p ++ signSuffix s) arg (packAlignExp p)]
  | .floatLoad t arg => [memInstr (floatTypeText t ++ ".load") arg (floatAlignExp t)]
  | .intStore t none arg => [memInstr (intTypeText t ++ ".store") arg (intAlignExp t)]
  | .intStore t (some p) arg =>
    [memInstr (intTypeText t ++ ".store" ++ packText p) arg (packAlignExp p)]
  | .floatStore t arg => [memInstr (floatTypeText t ++ ".store") arg (floatAlignExp t)]
  | .memorySize => ["memory.size"]
  | .memoryGrow => ["memory.grow"]
  | .memoryFill => ["memory.fill"]
  | .memoryCopy => ["memory.copy"]
  | .intConst t b => [intTypeText t ++ ".const " ++ bitsConst b]
  | .floatConst t b => [floatTypeText t ++ ".const " ++ floatConstText t b]
  | .intUnOp t op => [intTypeText t ++ "." ++ intUnOpText op]
  | .intBinOp t op => [intTypeText t ++ "." ++ intBinOpText op]
  | .intTestOp t op => [intTypeText t ++ "." ++ intTestOpText op]
  | .intRelOp t op => [intTypeText t ++ "." ++ intRelOpText op]
  | .floatUnOp t op => [floatTypeText t ++ "." ++ floatUnOpText op]
  | .floatBinOp t op => [floatTypeText t ++ "." ++ floatBinOpText op]
  | .floatRelOp t op => [floatTypeText t ++ "." ++ floatRelOpText op]
  | .convert op => [convertOpText op]

/-- Lines of an instruction sequence (nested bodies laid out by `nest`). -/
def exprLinesWith (nest : List String → List String) : List Lime1.Instr → List String
  | [] => []
  | i :: is => instrLinesWith nest i ++ exprLinesWith nest is

end

/-- Lines of one instruction, nested bodies indented by one level. -/
def instrLines (i : Lime1.Instr) : List String := instrLinesWith (indent 1) i

/-- Lines of an instruction sequence, nested bodies indented by one level. -/
def exprLines (e : Lime1.Expr) : List String := exprLinesWith (indent 1) e

/-- An instruction sequence on one line (for initializers and offsets): the lines of the
unindented layout joined by single spaces, so a nested `block … end` adds no extra
spaces. -/
def exprInline (e : Lime1.Expr) : String := spaced (exprLinesWith id e)

/-! ## Module fields -/

/-- `(type (func …))`. -/
def typeField (t : Lime1.FuncType) : List String := [sexp "type" [funcTypeText t]]

/-- Import descriptor `(func (type N))`, `(table …)`, `(memory …)`, `(global …)`. -/
def importDescText : Lime1.ImportDesc → String
  | .func t => sexp "func" [sexp "type" [idx t]]
  | .table t => sexp "table" [tableTypeText t]
  | .memory t => sexp "memory" [memoryTypeText t]
  | .global t => sexp "global" [globalTypeText t]

/-- `(import "m" "n" desc)`. -/
def importField (i : Lime1.Import) : List String :=
  [sexp "import" [name i.moduleName, name i.name, importDescText i.desc]]

/-- `(func (type N) (local …)` then the indented body, closed on its last line. -/
def funcField (f : Lime1.Func) : List String :=
  let locals := match f.locals with
    | [] => ""
    | ls => sexp "local" (ls.map v1ValType)
  closeLast (spaced ["(func", sexp "type" [idx f.type], locals] :: indent 1 (exprLines f.body))

/-- `(table min max? funcref)`. -/
def tableField (t : Lime1.TableType) : List String := [sexp "table" [tableTypeText t]]

/-- `(memory min max?)`. -/
def memoryField (t : Lime1.MemoryType) : List String := [sexp "memory" [memoryTypeText t]]

/-- `(global type init…)`. -/
def globalField (g : Lime1.Global) : List String :=
  [sexp "global" [globalTypeText g.type, exprInline g.init]]

/-- Export descriptor `(func N)` etc. -/
def externIdxText : Lime1.ExternIdx → String
  | .func i => sexp "func" [idx i]
  | .table i => sexp "table" [idx i]
  | .memory i => sexp "memory" [idx i]
  | .global i => sexp "global" [idx i]

/-- `(export "n" desc)`. -/
def exportField (e : Lime1.Export) : List String :=
  [sexp "export" [name e.name, externIdxText e.index]]

/-- `(start N)` if present. -/
def startField : Option FuncIdx → List String
  | none => []
  | some f => [sexp "start" [idx f]]

/-- `(elem (table N)? (offset …) func i*)`; `(table 0)` is left implicit. -/
def elemField (e : Lime1.Elem) : List String :=
  let table := if e.table.value.val = 0 then "" else sexp "table" [idx e.table]
  [sexp "elem" ([table, sexp "offset" [exprInline e.offset], "func"] ++ e.init.map idx)]

/-- `(data (memory N)? (offset …) "bytes")`; `(memory 0)` is left implicit. -/
def dataField (d : Lime1.Data) : List String :=
  let mem := if d.memory.value.val = 0 then "" else sexp "memory" [idx d.memory]
  [sexp "data" [mem, sexp "offset" [exprInline d.offset], string d.bytes.data.toList]]

/-- All module fields, in text order (imports before definitions). -/
def moduleFieldLines (m : Lime1.Module) : List String :=
  m.types.flatMap typeField ++ m.imports.flatMap importField ++ m.funcs.flatMap funcField ++
    m.tables.flatMap tableField ++ m.memories.flatMap memoryField ++
    m.globals.flatMap globalField ++ m.exports.flatMap exportField ++ startField m.start ++
    m.elems.flatMap elemField ++ m.data.flatMap dataField

/-! ## Small checks -/

theorem instrLines_if :
    instrLines (.if_ (.value .i32) [.intConst .i32 1] [.intConst .i32 2]) =
      ["if (result i32)", "  i32.const 1", "else", "  i32.const 2", "end"] := by
  decide +kernel

theorem instrLines_load8 :
    instrLines (.intLoad .i64 (some (.i8, .unsigned)) ⟨1, 4⟩) =
      ["i64.load8_u offset=4 align=2"] := by decide +kernel

theorem instrLines_f64_const :
    instrLines (.floatConst .f64 0x3ff0000000000000#64) = ["f64.const 0x1p+0"] := by
  decide +kernel

theorem convertOpText_truncSat :
    convertOpText (.truncSat .f64 .i32 .unsigned) = "i32.trunc_sat_f64_u" := by
  decide +kernel

/-- A one-line expression containing a block gets single spaces only. -/
theorem exprInline_block :
    exprInline [.block (.value .i32) [.intConst .i32 1, .block .empty [.nop]]] =
      "block (result i32) i32.const 1 block nop end end" := by
  decide +kernel

end Lime1Text

/-- Standard WebAssembly text of a Lime1 module (see the module docstring for the exact
layout). The empty module prints as `(module)`. -/
def printLime1Module (m : Lime1.Module) : String :=
  lines (closeLast ("(module" :: indent 1 (Lime1Text.moduleFieldLines m)))

theorem printLime1Module_empty : printLime1Module {} = "(module)" := by decide +kernel

end Silmaril.Wasm.Wat.Print
