module

public import Silmaril.Wasm.Binaryen.Exe.MemoryEncode
public import Silmaril.Wasm.Binaryen.Exe.FloatEncode
public import Silmaril.Wasm.Binaryen.Exe.SIMDEncode
public import Silmaril.Wasm.Binaryen.Exe.TableEncode
public import Silmaril.Wasm.Binaryen.Exe.TagEncode
public import Silmaril.Wasm.Binaryen.Exe.GcEncode
public import Silmaril.Wasm.Binary.Core.Modules

@[expose] public section

/-! # Executable binary encoder (the CERTIFIED end of `binaryen-lean`)

`encodeModule? : Module → Except String (List UInt8)` writes the canonical Core 3.0
binary of a module: minimal LEB128, no custom sections, empty sections omitted,
every recursive type group with one member written as a bare `functype`
(`RecType.single`/`SubType.plain`), runs of equal locals compressed.

The encoder covers the Binaryen profile (`Silmaril.Wasm.Binaryen.Syntax`, `Profile.lean`):
scalar numeric value types, function types, function, memory and global imports,
globals, function, global and memory exports, a start function, scalar memory
instructions, bulk memory and scalar conversions, 32-bit or 64-bit memories (defined or imported), and data
segments (active and passive). Memory accesses support nonzero indices and 64-bit offsets.
Anything else is reported with `.error`, never silently mis-encoded. Shared
memories remain unsupported. Funcref tables, table imports/exports, function-index
element segments and `call_indirect` are also supported. Tag definitions (section 13),
imports and exports use the exception attribute `0x00` and type/tag indices.
`throw` writes opcode `0x08` and its tag index, `throw_ref` `0x0A`, and `try_table`
`0x1F`, its block type, its catch clauses (`encCatch`) and its body.

The data count section is a policy bit of `encodeModuleWith? dataCount`. With
`dataCount = true` (`encodeModule?`, the round trip's canonical form) a module with data
segments gets one (Binaryen writes one whenever bulk memory is enabled, its default).
With `false` it is omitted, which the grammar allows only when the code mentions no data
index. The output encoder `encodeModule` writes it exactly when the code needs it
(`memory.init`/`data.drop`), so an input without one does not grow by its three bytes. A
module without segments never gets one.

Side conditions of the grammar that do not hold for every abstract module are
**runtime checks** here, never hypotheses of the soundness theorem:

* every vector length, section size and code-entry size fits in `u32` (`encU32`);
* a function has fewer than `2^32` locals (5.4:129–131);
* with no data count section, the code mentions no data index (5.4:195).

Indices are `Fin (2^32)`, so they always fit.

Soundness (`EncodeSound.lean`): `encodeModule? m = .ok bs → Binary.Core.Encodes bs m`,
against the SpecTec-transcribed grammar of `Silmaril/Wasm/Binary/Core/Modules.lean`.
See `Silmaril.Wasm.Binaryen.Exe.OptCompatMain` for the trust story.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm

def encIntType : IntType → UInt8
  | .i32 => 0x7F
  | .i64 => 0x7E

/-- Value types of the profile (`i32`, `i64`, `f32`, `f64`, `v128` and references). -/
def encValType : ValType → Except String (List UInt8)
  | .num (.int t) => pure [encIntType t]
  | .num (.float t) => pure [encFloatType t]
  | .vec .v128 => pure [0x7B]
  | .ref r => pure (encRefType r)

def encBlockType : BlockType → Except String (List UInt8)
  | .empty => pure [0x40]
  | .value t => encValType t
  | .typeIdx x => pure (encS x.toNat)

def signedOff : Signedness → Nat
  | .signed => 0
  | .unsigned => 1

/-- The opcode of an integer unary operator. -/
def intUnOpcode : IntType → IntUnOp → Except String UInt8
  | .i32, .clz => pure 0x67
  | .i32, .ctz => pure 0x68
  | .i32, .popcnt => pure 0x69
  | .i64, .clz => pure 0x79
  | .i64, .ctz => pure 0x7A
  | .i64, .popcnt => pure 0x7B
  | .i32, .extend .i8 => pure 0xC0
  | .i32, .extend .i16 => pure 0xC1
  | .i64, .extend .i8 => pure 0xC2
  | .i64, .extend .i16 => pure 0xC3
  | .i64, .extend .i32 => pure 0xC4
  | t, o => throw s!"encoder: invalid unary operator {repr t} {repr o}"

/-- Offset of a binary operator inside its type's opcode block (`0x6A`/`0x7C`). -/
def intBinOff : IntBinOp → Nat
  | .add => 0 | .sub => 1 | .mul => 2
  | .div s => 3 + signedOff s
  | .rem s => 5 + signedOff s
  | .and => 7 | .or => 8 | .xor => 9 | .shl => 10
  | .shr s => 11 + signedOff s
  | .rotl => 13 | .rotr => 14

/-- Offset of a relational operator after `eqz` (`0x46`/`0x51`). -/
def intRelOff : IntRelOp → Nat
  | .eq => 0 | .ne => 1
  | .lt s => 2 + signedOff s
  | .gt s => 4 + signedOff s
  | .le s => 6 + signedOff s
  | .ge s => 8 + signedOff s

def intTypeBase (t : IntType) (b32 b64 : Nat) : UInt8 :=
  match t with
  | .i32 => UInt8.ofNat b32
  | .i64 => UInt8.ofNat b64

mutual
/-- Instructions of the profile, recursively. -/
def encInstr : Instr → Except String (List UInt8)
  | .unreachable => pure [0x00]
  | .nop => pure [0x01]
  | .throw x => pure ([0x08] ++ encIdx x)
  | .throwRef => pure [0x0A]
  | .block bt body => do
      pure ([0x02] ++ (← encBlockType bt) ++ (← encInstrs body) ++ [0x0B])
  | .loop bt body => do
      pure ([0x03] ++ (← encBlockType bt) ++ (← encInstrs body) ++ [0x0B])
  | .if_ bt t e => do
      let bt' ← encBlockType bt
      let t' ← encInstrs t
      let e' ← encInstrs e
      if e.isEmpty then pure ([0x04] ++ bt' ++ t' ++ [0x0B])
      else pure ([0x04] ++ bt' ++ t' ++ [0x05] ++ e' ++ [0x0B])
  | .tryTable bt cs body => do
      pure ([0x1F] ++ (← encBlockType bt) ++ (← encVec (fun c => pure (encCatch c)) cs) ++
        (← encInstrs body) ++ [0x0B])
  | .br l => pure ([0x0C] ++ encIdx l)
  | .brIf l => pure ([0x0D] ++ encIdx l)
  | .brTable ls l => do
      pure ([0x0E] ++ (← encVec (fun x => pure (encIdx x)) ls) ++ encIdx l)
  | .return_ => pure [0x0F]
  | .call f => pure ([0x10] ++ encIdx f)
  | .callIndirect x y => do pure ([0x11] ++ encIdx y ++ (← encTableIdx x))
  | .returnCall f => pure ([0x12] ++ encIdx f)
  | .returnCallIndirect x y => pure ([0x13] ++ encIdx y ++ encIdx x)
  | .callRef x => pure ([0x14] ++ encIdx x)
  | .returnCallRef x => pure ([0x15] ++ encIdx x)
  | .drop => pure [0x1A]
  | .select none => pure [0x1B]
  | .refNull ht => pure ([0xD0] ++ encHeapType ht)
  | .refIsNull => pure [0xD1]
  | .refFunc f => pure ([0xD2] ++ encIdx f)
  | .localGet x => pure ([0x20] ++ encIdx x)
  | .localSet x => pure ([0x21] ++ encIdx x)
  | .localTee x => pure ([0x22] ++ encIdx x)
  | .globalGet x => pure ([0x23] ++ encIdx x)
  | .globalSet x => pure ([0x24] ++ encIdx x)
  | .tableGet x => pure ([0x25] ++ encIdx x)
  | .tableSet x => pure ([0x26] ++ encIdx x)
  | .tableInit x e => pure ([0xFC, 0x0C] ++ encIdx e ++ encIdx x)
  | .elemDrop e => pure ([0xFC, 0x0D] ++ encIdx e)
  | .tableCopy dst src => pure ([0xFC, 0x0E] ++ encIdx dst ++ encIdx src)
  | .tableGrow x => pure ([0xFC, 0x0F] ++ encIdx x)
  | .tableSize x => pure ([0xFC, 0x10] ++ encIdx x)
  | .tableFill x => pure ([0xFC, 0x11] ++ encIdx x)
  | .intLoad t p x a => do pure ([← intLoadOpcode t p] ++ (← encMemArg x a))
  | .intStore t p x a => do pure ([← intStoreOpcode t p] ++ (← encMemArg x a))
  | .memorySize x => do pure ([0x3F] ++ (← encMemoryIdx x))
  | .memoryGrow x => do pure ([0x40] ++ (← encMemoryIdx x))
  | .memoryInit x d => do pure ([0xFC, 0x08] ++ encIdx d ++ (← encMemoryIdx x))
  | .dataDrop d => pure ([0xFC, 0x09] ++ encIdx d)
  | .memoryCopy dst src => do
      pure ([0xFC, 0x0A] ++ (← encMemoryIdx dst) ++ (← encMemoryIdx src))
  | .memoryFill x => do pure ([0xFC, 0x0B] ++ (← encMemoryIdx x))
  | .floatLoad t x a => do pure ([floatTypeBase t 0x2A 0x2B] ++ (← encMemArg x a))
  | .floatStore t x a => do pure ([floatTypeBase t 0x38 0x39] ++ (← encMemArg x a))
  | .floatConst t b => pure ([floatTypeBase t 0x43 0x44] ++ encFloatBits t b)
  | .floatUnOp t o => pure [floatTypeBase t (0x8B + floatUnOff o) (0x99 + floatUnOff o)]
  | .floatBinOp t o => pure [floatTypeBase t (0x92 + floatBinOff o) (0xA0 + floatBinOff o)]
  | .floatRelOp t o => pure [floatTypeBase t (0x5B + floatRelOff o) (0x61 + floatRelOff o)]
  | .intConst t b => pure ([intTypeBase t 0x41 0x42] ++ encS b.toInt)
  | .intTestOp t .eqz => pure [intTypeBase t 0x45 0x50]
  | .intRelOp t o => pure [intTypeBase t (0x46 + intRelOff o) (0x51 + intRelOff o)]
  | .intUnOp t o => do pure [← intUnOpcode t o]
  | .intBinOp t o => pure [intTypeBase t (0x6A + intBinOff o) (0x7C + intBinOff o)]
  | .convert o => pure (encConvert o)
  | .select (some ts) => do pure ([0x1C] ++ (← encVec encValType ts))
  | .refEq => pure [0xD3]
  | .refAsNonNull => pure [0xD4]
  | .brOnNull l => pure ([0xD5] ++ encIdx l)
  | .brOnNonNull l => pure ([0xD6] ++ encIdx l)
  | .structNew x => pure ([0xFB, 0] ++ encIdx x)
  | .structNewDefault x => pure ([0xFB, 1] ++ encIdx x)
  | .structGet none x i => pure ([0xFB, 2] ++ encIdx x ++ encIdx i)
  | .structGet (some .signed) x i => pure ([0xFB, 3] ++ encIdx x ++ encIdx i)
  | .structGet (some .unsigned) x i => pure ([0xFB, 4] ++ encIdx x ++ encIdx i)
  | .structSet x i => pure ([0xFB, 5] ++ encIdx x ++ encIdx i)
  | .arrayNew x => pure ([0xFB, 6] ++ encIdx x)
  | .arrayNewDefault x => pure ([0xFB, 7] ++ encIdx x)
  | .arrayNewFixed x n => pure ([0xFB, 8] ++ encIdx x ++ encU n.val)
  | .arrayNewData x y => pure ([0xFB, 9] ++ encIdx x ++ encIdx y)
  | .arrayNewElem x y => pure ([0xFB, 10] ++ encIdx x ++ encIdx y)
  | .arrayGet none x => pure ([0xFB, 11] ++ encIdx x)
  | .arrayGet (some .signed) x => pure ([0xFB, 12] ++ encIdx x)
  | .arrayGet (some .unsigned) x => pure ([0xFB, 13] ++ encIdx x)
  | .arraySet x => pure ([0xFB, 14] ++ encIdx x)
  | .arrayLen => pure [0xFB, 15]
  | .arrayFill x => pure ([0xFB, 16] ++ encIdx x)
  | .arrayCopy x y => pure ([0xFB, 17] ++ encIdx x ++ encIdx y)
  | .arrayInitData x y => pure ([0xFB, 18] ++ encIdx x ++ encIdx y)
  | .arrayInitElem x y => pure ([0xFB, 19] ++ encIdx x ++ encIdx y)
  | .refTest ⟨false, ht⟩ => pure ([0xFB, 20] ++ encHeapType ht)
  | .refTest ⟨true, ht⟩ => pure ([0xFB, 21] ++ encHeapType ht)
  | .refCast ⟨false, ht⟩ => pure ([0xFB, 22] ++ encHeapType ht)
  | .refCast ⟨true, ht⟩ => pure ([0xFB, 23] ++ encHeapType ht)
  | .brOnCast l ⟨n₁, h₁⟩ ⟨n₂, h₂⟩ =>
    pure ([0xFB, 24, encCastOp n₁ n₂] ++ encIdx l ++ encHeapType h₁ ++ encHeapType h₂)
  | .brOnCastFail l ⟨n₁, h₁⟩ ⟨n₂, h₂⟩ =>
    pure ([0xFB, 25, encCastOp n₁ n₂] ++ encIdx l ++ encHeapType h₁ ++ encHeapType h₂)
  | .anyConvertExtern => pure [0xFB, 26]
  | .externConvertAny => pure [0xFB, 27]
  | .refI31 => pure [0xFB, 28]
  | .i31Get .signed => pure [0xFB, 29]
  | .i31Get .unsigned => pure [0xFB, 30]
  | .vecConst b => pure ([0xFD, 0x0C] ++ encLE 16 b.toNat)
  | i => encSIMDInstr i
/-- `encInstr` on a list. -/
def encInstrs : List Instr → Except String (List UInt8)
  | [] => pure []
  | i :: is => do pure ((← encInstr i) ++ (← encInstrs is))
end

/-- An expression: its instructions, then `end`. -/
def encExpr (e : Expr) : Except String (List UInt8) := do
  pure ((← encInstrs e) ++ [0x0B])

def encFuncType (ft : FuncType) : Except String (List UInt8) := do
  pure ([0x60] ++ (← encVec encValType ft.params) ++ (← encVec encValType ft.results))

def encMut : Mutability → UInt8
  | .const => 0x00
  | .var => 0x01

/-- Storage types: a value type or a packed type (5.2:59–61). -/
def encStorageType : StorageType → Except String (List UInt8)
  | .val t => encValType t
  | .packed p => pure [encPackType p]

/-- A field: its storage type, then its mutability (5.2:63–64). -/
def encFieldType (ft : FieldType) : Except String (List UInt8) := do
  pure ((← encStorageType ft.storage) ++ [encMut ft.mutability])

/-- Composite types: function, struct and array types (5.2:66–69). -/
def encCompType : CompositeType → Except String (List UInt8)
  | .func ft => encFuncType ft
  | .struct fs => do pure ([0x5F] ++ (← encVec encFieldType fs))
  | .array f => do pure ([0x5E] ++ (← encFieldType f))

/-- Sub types (5.2:71–74): a final type without supertypes is written bare, every
other one with `0x4F` (final) or `0x50` (open) and its supertypes. -/
def encSubType (st : SubType) : Except String (List UInt8) :=
  if st.final_ && st.supertypes.isEmpty then encCompType st.body
  else do
    pure ([if st.final_ then 0x4F else 0x50] ++
      (← encVec (fun x => pure (encIdx x)) st.supertypes) ++ (← encCompType st.body))

/-- A type-section entry (5.2:76–78): a group of one sub type is written as that sub
type, every other group with `0x4E`. -/
def encRecType (r : RecType) : Except String (List UInt8) :=
  match r.types with
  | [st] => encSubType st
  | sts => do pure ([0x4E] ++ (← encVec encSubType sts))

def encImport : Import → Except String (List UInt8)
  | ⟨mn, nm, .func x⟩ => do pure ((← encName mn) ++ (← encName nm) ++ ([0x00] ++ encIdx x))
  | ⟨mn, nm, .table tt⟩ => do
    pure ((← encName mn) ++ (← encName nm) ++ ([0x01] ++ (← encTableType tt)))
  | ⟨mn, nm, .memory mt⟩ => do
    pure ((← encName mn) ++ (← encName nm) ++ ([0x02] ++ (← encMemory mt)))
  | ⟨mn, nm, .global gt⟩ => do
    pure ((← encName mn) ++ (← encName nm) ++
      ([0x03] ++ ((← encValType gt.value) ++ [encMut gt.mutability])))
  | ⟨mn, nm, .tag t⟩ => do
    pure ((← encName mn) ++ (← encName nm) ++ ([0x04] ++ encTagType t))

def encGlobal (g : Global) : Except String (List UInt8) := do
  pure ((← encValType g.type.value) ++ [encMut g.type.mutability] ++ (← encExpr g.init))

def encExport : Export → Except String (List UInt8)
  | ⟨nm, .func x⟩ => do pure ((← encName nm) ++ ([0x00] ++ encIdx x))
  | ⟨nm, .table x⟩ => do pure ((← encName nm) ++ ([0x01] ++ encIdx x))
  | ⟨nm, .memory x⟩ => do pure ((← encName nm) ++ ([0x02] ++ encIdx x))
  | ⟨nm, .global x⟩ => do pure ((← encName nm) ++ ([0x03] ++ encIdx x))
  | ⟨nm, .tag x⟩ => do pure ((← encName nm) ++ ([0x04] ++ encIdx x))

/-- An expression element segment with an explicit reference type (kinds 5–7).
Unlike the compact function-index forms, these forms allow any encodable
initializer expression, including `global.get` of a non-nullable function. -/
def encElemExpressions (e : Elem) : Except String (List UInt8) := do
  let v ← encVec encExpr e.init
  match e.mode with
  | .active x off => pure (encU 6 ++ encIdx x ++ (← encExpr off) ++ encRefType e.type ++ v)
  | .passive => pure (encU 5 ++ encRefType e.type ++ v)
  | .declarative => pure (encU 7 ++ encRefType e.type ++ v)

/-- A function-index segment (kinds 0–3), a nullable funcref expression segment
(kinds 4–7; active table-0 segments use the implicit-table form), or an expression
segment of any other reference type (kinds 5–7, `encRefType`). Non-nullable
funcref initializers use function indices when possible and the expression form
otherwise. -/
def encElem (e : Elem) : Except String (List UInt8) :=
  if e.type = ⟨false, .abstract .func⟩ then
    match elemFuncs? e.init with
    | some ys => do
      let v ← encVec (fun y => pure (encIdx y)) ys
      match e.mode with
      | .active x off =>
        if x.toNat = 0 then pure (encU 0 ++ (← encExpr off) ++ v)
        else pure (encU 2 ++ encIdx x ++ (← encExpr off) ++ [0x00] ++ v)
      | .passive => pure (encU 1 ++ [0x00] ++ v)
      | .declarative => pure (encU 3 ++ [0x00] ++ v)
    | none => encElemExpressions e
  else if e.type = ⟨true, .abstract .func⟩ then do
    let v ← encVec encExpr e.init
    match e.mode with
    | .active x off =>
      if x.toNat = 0 then pure (encU 4 ++ (← encExpr off) ++ v)
      else pure (encU 6 ++ encIdx x ++ (← encExpr off) ++ [0x70] ++ v)
    | .passive => pure (encU 5 ++ [0x70] ++ v)
    | .declarative => pure (encU 7 ++ [0x70] ++ v)
  else encElemExpressions e

/-- A data segment: kind `0` (active in memory 0), `1` (passive) or `2` (active in
another memory), then its bytes as a byte vector. -/
def encData (d : Data) : Except String (List UInt8) := do
  let bs := d.bytes.data.toList
  let v ← encU32 bs.length
  match d.mode with
  | .passive => pure (encU 1 ++ (v ++ bs))
  | .active x e =>
    if x.toNat = 0 then pure (encU 0 ++ (← encExpr e) ++ (v ++ bs))
    else pure (encU 2 ++ encIdx x ++ (← encExpr e) ++ (v ++ bs))

/-- Run-length groups of equal adjacent locals. -/
def groupLocals : List ValType → List (Nat × ValType)
  | [] => []
  | t :: ts =>
    match groupLocals ts with
    | (n, t') :: rest => if t = t' then (n + 1, t) :: rest else (1, t) :: (n, t') :: rest
    | [] => [(1, t)]

def encLocals (ls : List ValType) : Except String (List UInt8) :=
  encVec (fun (p : Nat × ValType) => do pure ((← encU32 p.1) ++ (← encValType p.2)))
    (groupLocals ls)

/-- A code entry: its size, then the compressed locals and the body. Fails on `2^32`
or more locals (5.4:129–131). -/
def encCode (f : Func) : Except String (List UInt8) :=
  if f.locals.length < 2 ^ 32 then do
    let l ← encLocals f.locals
    let e ← encExpr f.body
    let n ← encU32 (l ++ e).length
    pure (n ++ (l ++ e))
  else throw "encoder: a function has 2^32 or more locals"

/-- The start section's body. -/
def encStart : Option FuncIdx → List UInt8
  | some x => encIdx x
  | none => []

/-- The header: magic and version. -/
def header : List UInt8 := [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]

/-- Whether a module's code mentions a data index (`memory.init`, `data.drop`), which
requires a data count section (5.4:195). -/
def usesDataIdx (m : Module) : Bool :=
  !(Binary.Core.codesDataIdxs (m.funcs.map fun f => (f.locals, f.body))).isEmpty

/-- **The executable encoder**, with the data count section written when `dataCount` holds
and there are data segments. Fails when the section is omitted but the code mentions a
data index. -/
def encodeModuleWith? (dataCount : Bool) (m : Module) : Except String (List UInt8) :=
  if (dataCount && !m.data.isEmpty) ||
      (Binary.Core.codesDataIdxs (m.funcs.map fun f => (f.locals, f.body))).isEmpty then do
    let ty ← encVec encRecType m.types
    let im ← encVec encImport m.imports
    let fn ← encVec (fun f => pure (encIdx f.type)) m.funcs
    let me ← encVec encMemory m.memories
    let tg ← encVec (fun t => pure (encTagType t)) m.tags
    let gl ← encVec encGlobal m.globals
    let ex ← encVec encExport m.exports
    let co ← encVec encCode m.funcs
    let da ← encVec encData m.data
    let dc ← encU32 m.data.length
    let tb ← encVec (encTableWith encExpr) m.tables
    let el ← encVec encElem m.elems
    let s1 ← encSection 1 m.types.length ty
    let s2 ← encSection 2 m.imports.length im
    let s3 ← encSection 3 m.funcs.length fn
    let s4 ← encSection 4 m.tables.length tb
    let s5 ← encSection 5 m.memories.length me
    let s13 ← encSection 13 m.tags.length tg
    let s6 ← encSection 6 m.globals.length gl
    let s7 ← encSection 7 m.exports.length ex
    let s8 ← encSection 8 (if m.start.isSome then 1 else 0) (encStart m.start)
    let s9 ← encSection 9 m.elems.length el
    let s12 ← encSection 12 (if dataCount && !m.data.isEmpty then 1 else 0) dc
    let s10 ← encSection 10 m.funcs.length co
    let s11 ← encSection 11 m.data.length da
    pure (header ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s13 ++ s6 ++ s7 ++ s8 ++ s9 ++ s12 ++ s10 ++ s11)
  else
    throw "encoder: data indices without a data count section are not supported"

/-- Canonical bytes of a module of the supported fragment, with a data count section
whenever there are data segments. -/
def encodeModule? (m : Module) : Except String (List UInt8) :=
  encodeModuleWith? true m

/-- Whether the binary module `b` has a data count section (id 12), by a walk over its
top-level sections past the header; each section size is an unsigned LEB128. Anything
malformed gives `false`. The result is a hint only: soundness holds for either policy. -/
def hasDataCountSection (b : ByteArray) : Bool :=
  go b.size 8
where
  /-- The unsigned LEB128 at `i` (at most `k` bytes) and the position after it. -/
  leb : Nat → Nat → Nat → Nat → Option (Nat × Nat)
    | 0, _, _, _ => none
    | k + 1, i, acc, sh =>
      match b[i]? with
      | none => none
      | some x =>
        let acc := acc + (x.toNat % 128) <<< sh
        if x < 0x80 then some (acc, i + 1) else leb k (i + 1) acc (sh + 7)
  go : Nat → Nat → Bool
    | 0, _ => false
    | fuel + 1, i =>
      match b[i]? with
      | none => false
      | some id =>
        id == 12 || match leb 5 (i + 1) 0 0 with
          | some (n, j) => go fuel (j + n)
          | none => false

/-- The output encoder as a `ByteArray`. The data count section follows the input
bytes `input` (a hint only): it is written when the input has one and there are data
segments, or when the code mentions a data index. So an unchanged module re-encodes to
its input, and linker output without the section does not grow by its three bytes. -/
def encodeModule (input : ByteArray) (m : Module) : Except String ByteArray :=
  (encodeModuleWith? (usesDataIdx m || hasDataCountSection input) m).map fun bs => ⟨bs.toArray⟩

end Silmaril.Wasm.Binaryen.Exe
