module

public import Silmaril.Wasm.ByteParse.Defs

/-!
# WebAssembly component binaries: abstract syntax and grammar

The abstract syntax of the component-model binary format (`Binary.md` of the
component-model repository, revision below) and its grammar, built from the verified
combinators of `Silmaril.Wasm.ByteParse`. Every `Grammar` here pairs its parser with the
grammar; the proofs that the parser is sound and complete for it are the `Grammar.Lawful`
instances of `Silmaril.Proofs.Wasm.Component.Binary.Lawful` (exported by
`Silmaril.Wasm.Component.Binary.Thms`).

```
component ::= preamble section*            preamble ::= 00 61 73 6d  0d 00  01 00
section   ::= 0x00 size custom  | 0x01 size core:module | 0x02 size vec(core:instance)
            | 0x03 size vec(core:type) | 0x04 size component | 0x05 size vec(instance)
            | 0x06 size vec(alias) | 0x07 size vec(type) | 0x08 size vec(canon)
            | 0x09 size start | 0x0a size vec(import) | 0x0b size vec(export)
            | 0x0c size vec(value)
```

Each section body must fill its `size` exactly (`Grammar.sizedBy`).

## Coverage

* core modules are kept as bytes (`Section.coreModule`); `Lower` decodes them
  with silmaril's verified core decoder;
* core types: function types (`0x60`, i.e. singleton final rec types) and
  module types (`0x50`) whose declarations import/export functions, tables
  (`0x00`/`0x01` limits), memories, globals and tags, with function-type
  `type` declarations and outer type aliases (`0x10 0x01`); other GC
  recursive types and the `0x00 0x50` sub form are not supported;
* component types: all primitive and compound value types (including
  `own`/`borrow`, fixed-size lists, `stream`/`future`, `map`), sync and async
  function types, component and instance types, resources;
* `canon`: `lift`, `lower`, `resource.new/drop/rep`; the async, stream,
  future, error-context, waitable and thread built-ins are reported as
  unknown tags;
* names: all three `nameattributes` forms, with `implements`,
  `version-suffix` and `external-id` attributes.

The grammar follows `design/mvp/Binary.md` of WebAssembly/component-model at
commit `8505ba73dda2775b9438c0b8d169b96a556f864a` (2026-10-27).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary

open Silmaril.Wasm.ByteParse (Grammar GrammarE NonEmpty StartsWith Bytes Error runAll)

/-! ## Abstract syntax -/

/-- `core:sort`. -/
inductive CoreSort where
  | func | table | memory | global | tag | type | module | instance
  deriving Repr, DecidableEq, Inhabited

/-- `sort`. -/
inductive ItemSort where
  | core (s : CoreSort)
  | func | value | type | component | instance
  deriving Repr, DecidableEq, Inhabited

/-- `core:sortidx`. -/
structure CoreSortIdx where
  sort : CoreSort
  idx : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `sortidx`. -/
structure SortIdx where
  sort : ItemSort
  idx : Nat
  deriving Repr, DecidableEq, Inhabited

/-- An attribute of an import/export name (`attribute`). -/
inductive Attribute where
  /-- `0x00 interfacename`: `(implements "…")`. -/
  | implements (name : String)
  /-- `0x01 semversuffix`: `(version-suffix "…")`. -/
  | versionSuffix (suffix : String)
  /-- `0x02 name`: `(external-id …)`. -/
  | externalId (id : String)
  deriving Repr, DecidableEq, Inhabited

/-- The spelling of `nameattributes`: the redundant `0x00`/`0x01` forms, or
`0x02` with attributes. -/
inductive NameForm where
  | plain0
  | plain1
  | attrs (as : List Attribute)
  deriving Repr, DecidableEq, Inhabited

/-- `nameattributes`: an import/export name and its spelling. -/
structure ExternName where
  name : String
  form : NameForm := .plain0
  deriving Repr, DecidableEq, Inhabited

instance : Coe String ExternName := ⟨fun s => ⟨s, .plain0⟩⟩

/-- `core:instanceexpr`. -/
inductive CoreInstanceExpr where
  /-- `0x00 m:moduleidx vec(name 0x12 instanceidx)`. -/
  | instantiate (module : Nat) (args : List (String × Nat))
  /-- `0x01 vec(name core:sortidx)`. -/
  | exports (es : List (String × CoreSortIdx))
  deriving Repr, DecidableEq, Inhabited

/-- `instanceexpr`. -/
inductive InstanceExpr where
  /-- `0x00 c:componentidx vec(string sortidx)`. -/
  | instantiate (component : Nat) (args : List (String × SortIdx))
  /-- `0x01 vec(nameattributes sortidx)`. -/
  | exports (es : List (ExternName × SortIdx))
  deriving Repr, DecidableEq, Inhabited

/-- `aliastarget`. -/
inductive AliasTarget where
  /-- `0x00 i:instanceidx n:string`. -/
  | export (inst : Nat) (name : String)
  /-- `0x01 i:core:instanceidx n:core:name`. -/
  | coreExport (inst : Nat) (name : String)
  /-- `0x02 ct:u32 idx:u32`. -/
  | outer (count idx : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `alias ::= sort aliastarget`. -/
structure Alias where
  sort : ItemSort
  target : AliasTarget
  deriving Repr, DecidableEq, Inhabited

/-- Core value types. -/
inductive CoreValType where
  | i32 | i64 | f32 | f64 | v128 | funcref | externref
  deriving Repr, DecidableEq, Inhabited

/-- Limits: `0x00 min` or `0x01 min max`. -/
structure Limits where
  min : Nat
  max : Option Nat
  deriving Repr, DecidableEq, Inhabited

/-- Core import/export descriptions. -/
inductive CoreImportDesc where
  | func (type : Nat)
  | table (elem : CoreValType) (limits : Limits)
  | memory (limits : Limits)
  | global (type : CoreValType) (mutable : Bool)
  | tag (type : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A core function type `0x60 vec(valtype) vec(valtype)`. -/
structure CoreFuncType where
  params : List CoreValType
  results : List CoreValType
  deriving Repr, DecidableEq, Inhabited

/-- `core:moduledecl`. -/
inductive ModuleDecl where
  /-- `0x00 module:name field:name desc`. -/
  | import (module name : String) (desc : CoreImportDesc)
  /-- `0x01 0x60 functype` (only function types). -/
  | type (t : CoreFuncType)
  /-- `0x02 0x10 0x01 ct idx`: an outer alias of a type. -/
  | alias (count idx : Nat)
  /-- `0x03 name desc`. -/
  | export (name : String) (desc : CoreImportDesc)
  deriving Repr, DecidableEq, Inhabited

/-- `core:type`. -/
inductive CoreType where
  | func (t : CoreFuncType)
  | module (decls : List ModuleDecl)
  deriving Repr, DecidableEq, Inhabited

/-- `primvaltype`. -/
inductive PrimValType where
  | bool | s8 | u8 | s16 | u16 | s32 | u32 | s64 | u64 | f32 | f64 | char | string
  | errorContext
  deriving Repr, DecidableEq, Inhabited

/-- `valtype ::= i:typeidx | pvt:primvaltype`. -/
inductive ValType where
  | prim (p : PrimValType)
  | idx (i : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `defvaltype`. -/
inductive DefValType where
  | prim (p : PrimValType)
  | record (fields : List (String × ValType))
  | variant (cases : List (String × Option ValType))
  | list (t : ValType)
  | tuple (ts : List ValType)
  | flags (labels : List String)
  | enum (labels : List String)
  | option (t : ValType)
  | result (ok err : Option ValType)
  | own (i : Nat)
  | borrow (i : Nat)
  | fixedList (t : ValType) (n : Nat)
  | stream (t : Option ValType)
  | future (t : Option ValType)
  | map (k v : ValType)
  deriving Repr, DecidableEq, Inhabited

/-- `functype ::= (0x40 | 0x43 async) paramlist resultlist`, with
`resultlist ::= 0x00 valtype | 0x01 0x00`. -/
structure FuncType where
  params : List (String × ValType)
  result : Option ValType
  async : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- `valuebound`. -/
inductive ValueBound where
  | eq (i : Nat)
  | type (t : ValType)
  deriving Repr, DecidableEq, Inhabited

/-- `typebound`. -/
inductive TypeBound where
  | eq (i : Nat)
  | subResource
  deriving Repr, DecidableEq, Inhabited

/-- `externdesc`. -/
inductive ExternDesc where
  | coreModule (i : Nat)
  | func (i : Nat)
  | value (b : ValueBound)
  | type (b : TypeBound)
  | component (i : Nat)
  | instance (i : Nat)
  deriving Repr, DecidableEq, Inhabited

mutual
/-- `deftype`. -/
inductive DefType where
  | val (d : DefValType)
  | func (f : FuncType)
  | component (decls : List ComponentDecl)
  | instance (decls : List InstanceDecl)
  | resource (rep : CoreValType) (dtor : Option Nat)

/-- `instancedecl`. -/
inductive InstanceDecl where
  | coreType (t : CoreType)
  | type (t : DefType)
  | alias (a : Alias)
  | export (name : ExternName) (desc : ExternDesc)

/-- `componentdecl`. -/
inductive ComponentDecl where
  | import (name : ExternName) (desc : ExternDesc)
  | inst (d : InstanceDecl)
end

/-- `canonopt`. -/
inductive CanonOpt where
  | utf8 | utf16 | latin1utf16
  | memory (i : Nat)
  | realloc (i : Nat)
  | postReturn (i : Nat)
  | async
  | callback (i : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `canon`. -/
inductive Canon where
  /-- `0x00 0x00 f:core:funcidx opts ft:typeidx`. -/
  | lift (coreFunc : Nat) (opts : List CanonOpt) (type : Nat)
  /-- `0x01 0x00 f:funcidx opts`. -/
  | lower (func : Nat) (opts : List CanonOpt)
  | resourceNew (t : Nat)
  | resourceDrop (t : Nat)
  | resourceRep (t : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `start ::= f:funcidx vec(valueidx) r:u32`. -/
structure Start where
  func : Nat
  args : List Nat
  results : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `import ::= importname' externdesc`. -/
structure Import where
  name : ExternName
  desc : ExternDesc
  deriving Repr, DecidableEq, Inhabited

/-- `export ::= exportname' sortidx externdesc?`. -/
structure Export where
  name : ExternName
  item : SortIdx
  desc : Option ExternDesc
  deriving Repr, DecidableEq, Inhabited

/-- `value ::= valtype len:u32 bytes` (kept as bytes). -/
structure Value where
  type : ValType
  bytes : ByteArray

mutual
/-- Sections. -/
inductive Section where
  | custom (name : String) (data : ByteArray)
  | coreModule (bytes : ByteArray)
  | coreInstances (xs : List CoreInstanceExpr)
  | coreTypes (xs : List CoreType)
  | component (c : Ast)
  | instances (xs : List InstanceExpr)
  | aliases (xs : List Alias)
  | types (xs : List DefType)
  | canons (xs : List Canon)
  | start (s : Start)
  | imports (xs : List Import)
  | exports (xs : List Export)
  | values (xs : List Value)

/-- A component: its sections in order. -/
inductive Ast where
  | mk (sections : List Section)
end

def Ast.sections : Ast → List Section | .mk ss => ss

instance : Inhabited Ast := ⟨.mk []⟩
instance : Inhabited DefType := ⟨.resource .i32 none⟩

/-! ## Grammar -/

section Grammar
open Silmaril.Wasm.ByteParse.Grammar

/-- The preamble bytes. -/
def preambleBytes : List UInt8 := [0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00]

/-- A tag with no payload. -/
@[inline] def tag0 {α : Type} (a : α) : Option (Grammar α) := some (Grammar.pure a)

def coreSortG : Grammar CoreSort := tagged "core:sort" fun b => match b.toNat with
  | 0x00 => tag0 .func | 0x01 => tag0 .table | 0x02 => tag0 .memory | 0x03 => tag0 .global
  | 0x04 => tag0 .tag | 0x10 => tag0 .type | 0x11 => tag0 .module | 0x12 => tag0 .instance | _ => none

def sortG : Grammar ItemSort := tagged "sort" fun b => match b.toNat with
  | 0x00 => some (coreSortG.map .core)
  | 0x01 => tag0 .func | 0x02 => tag0 .value | 0x03 => tag0 .type
  | 0x04 => tag0 .component | 0x05 => tag0 .instance | _ => none

def coreSortIdxG : Grammar CoreSortIdx := (coreSortG.seq u32).map fun p => ⟨p.1, p.2⟩

def sortIdxG : Grammar SortIdx := (sortG.seq u32).map fun p => ⟨p.1, p.2⟩

def attributeG : Grammar Attribute := tagged "attribute" fun b => match b.toNat with
  | 0x00 => some (name.map .implements)
  | 0x01 => some (name.map .versionSuffix)
  | 0x02 => some (name.map .externalId)
  | _ => none

/-- `nameattributes`. -/
def externNameG : Grammar ExternName := tagged "nameattributes" fun b => match b.toNat with
  | 0x00 => some (name.map fun n => ⟨n, .plain0⟩)
  | 0x01 => some (name.map fun n => ⟨n, .plain1⟩)
  | 0x02 => some ((name.seq (vec attributeG (tagged_nonEmpty _ _))).map fun p => ⟨p.1, .attrs p.2⟩)
  | _ => none

theorem externNameG_nonEmpty : NonEmpty externNameG.G := tagged_nonEmpty _ _
theorem coreSortG_nonEmpty : NonEmpty coreSortG.G := tagged_nonEmpty _ _
theorem sortG_nonEmpty : NonEmpty sortG.G := tagged_nonEmpty _ _

def coreInstArgG : Grammar (String × Nat) := name.seq ((expect "core:instantiatearg" 0x12).then_ u32)

def coreInlineExportG : Grammar (String × CoreSortIdx) := name.seq coreSortIdxG

def coreInstanceExprG : Grammar CoreInstanceExpr :=
  tagged "core:instanceexpr" fun b => match b.toNat with
  | 0x00 => some ((u32.seq (vec coreInstArgG (seq_nonEmpty name_nonEmpty))).map
      fun p => .instantiate p.1 p.2)
  | 0x01 => some ((vec coreInlineExportG (seq_nonEmpty name_nonEmpty)).map .exports)
  | _ => none

def instArgG : Grammar (String × SortIdx) := name.seq sortIdxG

def inlineExportG : Grammar (ExternName × SortIdx) := externNameG.seq sortIdxG

def instanceExprG : Grammar InstanceExpr :=
  tagged "instanceexpr" fun b => match b.toNat with
  | 0x00 => some ((u32.seq (vec instArgG (seq_nonEmpty name_nonEmpty))).map
      fun p => .instantiate p.1 p.2)
  | 0x01 => some ((vec inlineExportG (seq_nonEmpty externNameG_nonEmpty)).map .exports)
  | _ => none

def aliasTargetG : Grammar AliasTarget := tagged "aliastarget" fun b => match b.toNat with
  | 0x00 => some ((u32.seq name).map fun p => .export p.1 p.2)
  | 0x01 => some ((u32.seq name).map fun p => .coreExport p.1 p.2)
  | 0x02 => some ((u32.seq u32).map fun p => .outer p.1 p.2)
  | _ => none

def aliasG : Grammar Alias := (sortG.seq aliasTargetG).map fun p => ⟨p.1, p.2⟩

theorem aliasG_nonEmpty : NonEmpty aliasG.G := map_nonEmpty (seq_nonEmpty sortG_nonEmpty)

/-! ### Core types -/

def coreValTypeG : Grammar CoreValType := tagged "core:valtype" fun b => match b.toNat with
  | 0x7f => tag0 .i32 | 0x7e => tag0 .i64 | 0x7d => tag0 .f32 | 0x7c => tag0 .f64
  | 0x7b => tag0 .v128 | 0x70 => tag0 .funcref | 0x6f => tag0 .externref | _ => none

theorem coreValTypeG_nonEmpty : NonEmpty coreValTypeG.G := tagged_nonEmpty _ _

def limitsG : Grammar Limits := tagged "limits" fun b => match b.toNat with
  | 0x00 => some (u32.map fun n => ⟨n, none⟩)
  | 0x01 => some ((u32.seq u32).map fun p => ⟨p.1, some p.2⟩)
  | _ => none

def mutG : Grammar Bool := tagged "mut" fun b => match b.toNat with
  | 0x00 => tag0 false | 0x01 => tag0 true | _ => none

def coreImportDescG : Grammar CoreImportDesc := tagged "core:importdesc" fun b => match b.toNat with
  | 0x00 => some (u32.map .func)
  | 0x01 => some ((coreValTypeG.seq limitsG).map fun p => .table p.1 p.2)
  | 0x02 => some (limitsG.map .memory)
  | 0x03 => some ((coreValTypeG.seq mutG).map fun p => .global p.1 p.2)
  | 0x04 => some ((expect "tag attribute" 0x00).then_ (u32.map .tag))
  | _ => none

def coreFuncTypeBodyG : Grammar CoreFuncType :=
  ((vec coreValTypeG coreValTypeG_nonEmpty).seq (vec coreValTypeG coreValTypeG_nonEmpty)).map
    fun p => ⟨p.1, p.2⟩

def moduleDeclG : Grammar ModuleDecl := tagged "core:moduledecl" fun b => match b.toNat with
  | 0x00 => some (((name.seq name).seq coreImportDescG).map fun p => .import p.1.1 p.1.2 p.2)
  | 0x01 => some ((expect "core:functype" 0x60).then_ (coreFuncTypeBodyG.map .type))
  | 0x02 => some ((lit [0x10, 0x01]).then_ ((u32.seq u32).map fun p => .alias p.1 p.2))
  | 0x03 => some ((name.seq coreImportDescG).map fun p => .export p.1 p.2)
  | _ => none

def coreTypeG : Grammar CoreType := tagged "core:type" fun b => match b.toNat with
  | 0x60 => some (coreFuncTypeBodyG.map .func)
  | 0x50 => some ((vec moduleDeclG (tagged_nonEmpty _ _)).map .module)
  | _ => none

theorem coreTypeG_nonEmpty : NonEmpty coreTypeG.G := tagged_nonEmpty _ _

/-! ### Value types -/

/-- The byte of a primitive value type. -/
def PrimValType.byte : PrimValType → UInt8
  | .bool => 0x7f | .s8 => 0x7e | .u8 => 0x7d | .s16 => 0x7c | .u16 => 0x7b
  | .s32 => 0x7a | .u32 => 0x79 | .s64 => 0x78 | .u64 => 0x77 | .f32 => 0x76
  | .f64 => 0x75 | .char => 0x74 | .string => 0x73 | .errorContext => 0x64

/-- The primitive value type of a byte. -/
def PrimValType.ofByte? (b : UInt8) : Option PrimValType := match b.toNat with
  | 0x7f => some .bool | 0x7e => some .s8 | 0x7d => some .u8 | 0x7c => some .s16
  | 0x7b => some .u16 | 0x7a => some .s32 | 0x79 => some .u32 | 0x78 => some .s64
  | 0x77 => some .u64 | 0x76 => some .f32 | 0x75 => some .f64 | 0x74 => some .char
  | 0x73 => some .string | 0x64 => some .errorContext | _ => none

def primValTypeG : Grammar PrimValType :=
  tagged "primvaltype" fun b => (PrimValType.ofByte? b).map Grammar.pure

/-- A type index in a value type: a non-negative `s33` below `2 ^ 32`. -/
def typeIdxS33 (i : Int) : Option Nat := if 0 ≤ i ∧ i < 2 ^ 32 then some i.toNat else none

def isPrimByte (b : UInt8) : Bool := (PrimValType.ofByte? b).isSome

theorem primValTypeG_starts : StartsWith (fun b => isPrimByte b = true) (primValTypeG.map ValType.prim).G := by
  rintro l a ⟨p, ⟨b, l', G, rfl, hk, -⟩, -⟩
  refine ⟨b, l', rfl, ?_⟩
  simp only [isPrimByte]
  cases h : PrimValType.ofByte? b <;> simp_all

/-- A non-negative signed LEB128 starts below `0x40` or with a continuation bit,
so never with a primitive value type byte. -/
theorem sn_head_nonneg {N : Nat} {l : Bytes} {i : Int} (h : Silmaril.Wasm.Binary.SN N l i)
    (hi : 0 ≤ i) : ∃ b l', l = b :: l' ∧ (b.toNat < 0x40 ∨ 0x80 ≤ b.toNat) := by
  cases h with
  | pos n h1 _ => exact ⟨n, [], rfl, .inl (by simpa using h1)⟩
  | neg n h1 h2 _ =>
    exfalso
    have : (n.toNat : Int) < 2 ^ 7 := by exact_mod_cast h2
    omega
  | cont n h1 _ _ => exact ⟨n, _, rfl, .inr (by simpa using h1)⟩

theorem idxG_starts :
    StartsWith (fun b => isPrimByte b = false) ((sN 33).filterMap "typeidx" typeIdxS33 |>.map ValType.idx).G := by
  rintro l a ⟨n, ⟨i, hs, hf⟩, -⟩
  have hi : 0 ≤ i := by
    unfold typeIdxS33 at hf; split at hf
    · exact (by assumption : 0 ≤ i ∧ i < 2 ^ 32).1
    · cases hf
  obtain ⟨b, l', rfl, hb⟩ := sn_head_nonneg hs hi
  refine ⟨b, l', rfl, ?_⟩
  simp only [isPrimByte, PrimValType.ofByte?]
  split <;> simp_all

def valTypeG : Grammar ValType :=
  choice isPrimByte (primValTypeG.map .prim)
    ((sN 33).filterMap "typeidx" typeIdxS33 |>.map .idx) primValTypeG_starts idxG_starts

theorem valTypeG_nonEmpty : NonEmpty valTypeG.G := choice_nonEmpty

def labelValTypeG : Grammar (String × ValType) := name.seq valTypeG

theorem labelValTypeG_nonEmpty : NonEmpty labelValTypeG.G := seq_nonEmpty name_nonEmpty

def caseG : Grammar (String × Option ValType) :=
  name.bind fun n => (opt "case type" valTypeG).bind fun t =>
    (expect "case end" 0x00).map fun _ => (n, t)

/-- `resultlist ::= 0x00 valtype | 0x01 0x00`. -/
def resultListG : Grammar (Option ValType) := tagged "resultlist" fun b => match b.toNat with
  | 0x00 => some (valTypeG.map some)
  | 0x01 => some ((expect "resultlist" 0x00).then_ (Grammar.pure none))
  | _ => none

/-- `paramlist resultlist`, after the `0x40`/`0x43` tag giving `async`. -/
def funcTypeBodyG (async : Bool) : Grammar FuncType :=
  ((vec labelValTypeG labelValTypeG_nonEmpty).seq resultListG).map fun p => ⟨p.1, p.2, async⟩

/-- The bodies of compound value types, after their tag. -/
def defValTypeBody (b : UInt8) : Option (Grammar DefValType) :=
  match b.toNat with
  | 0x72 => some ((vec labelValTypeG labelValTypeG_nonEmpty).map .record)
  | 0x71 => some ((vec caseG (bind_nonEmpty name_nonEmpty)).map .variant)
  | 0x70 => some (valTypeG.map .list)
  | 0x6f => some ((vec valTypeG valTypeG_nonEmpty).map .tuple)
  | 0x6e => some ((vec name name_nonEmpty).map .flags)
  | 0x6d => some ((vec name name_nonEmpty).map .enum)
  | 0x6b => some (valTypeG.map .option)
  | 0x6a => some (((opt "result ok" valTypeG).seq (opt "result error" valTypeG)).map
      fun p => .result p.1 p.2)
  | 0x69 => some (u32.map .own)
  | 0x68 => some (u32.map .borrow)
  | 0x67 => some ((valTypeG.seq u32).map fun p => .fixedList p.1 p.2)
  | 0x66 => some ((opt "stream type" valTypeG).map .stream)
  | 0x65 => some ((opt "future type" valTypeG).map .future)
  | 0x63 => some ((valTypeG.seq valTypeG).map fun p => .map p.1 p.2)
  | _ => (PrimValType.ofByte? b).map fun p => Grammar.pure (.prim p)

def valueBoundG : Grammar ValueBound := tagged "valuebound" fun b => match b.toNat with
  | 0x00 => some (u32.map .eq) | 0x01 => some (valTypeG.map .type) | _ => none

def typeBoundG : Grammar TypeBound := tagged "typebound" fun b => match b.toNat with
  | 0x00 => some (u32.map .eq) | 0x01 => tag0 .subResource | _ => none

def externDescG : Grammar ExternDesc := tagged "externdesc" fun b => match b.toNat with
  | 0x00 => some ((expect "core module sort" 0x11).then_ (u32.map .coreModule))
  | 0x01 => some (u32.map .func)
  | 0x02 => some (valueBoundG.map .value)
  | 0x03 => some (typeBoundG.map .type)
  | 0x04 => some (u32.map .component)
  | 0x05 => some (u32.map .instance)
  | _ => none

def importG : Grammar Import := (externNameG.seq externDescG).map fun p => ⟨p.1, p.2⟩

/-! ### Type definitions (recursive, by depth) -/

def instanceDeclBody (t : Grammar DefType) (b : UInt8) : Option (Grammar InstanceDecl) :=
  match b.toNat with
  | 0x00 => some (coreTypeG.map .coreType)
  | 0x01 => some (t.map .type)
  | 0x02 => some (aliasG.map .alias)
  | 0x04 => some ((externNameG.seq externDescG).map fun p => .export p.1 p.2)
  | _ => none

def componentDeclBody (t : Grammar DefType) (b : UInt8) : Option (Grammar ComponentDecl) :=
  if b.toNat = 0x03 then some ((externNameG.seq externDescG).map fun p => .import p.1 p.2)
  else (instanceDeclBody t b).map (Grammar.map .inst)

/-- `resourcetype ::= 0x3f core:valtype funcidx?`, after the tag. -/
def resourceBodyG : Grammar (CoreValType × Option Nat) :=
  coreValTypeG.seq (opt "resource dtor" u32)

/-- `deftype`, nested at most `k` deep. -/
def defTypeG : Nat → Grammar DefType
  | 0 => fail
  | k + 1 => tagged "type" fun b => match b.toNat with
    | 0x40 => some ((funcTypeBodyG false).map .func)
    | 0x43 => some ((funcTypeBodyG true).map .func)
    | 0x41 => some ((vec (tagged "componentdecl" (componentDeclBody (defTypeG k)))
        (tagged_nonEmpty _ _)).map .component)
    | 0x42 => some ((vec (tagged "instancedecl" (instanceDeclBody (defTypeG k)))
        (tagged_nonEmpty _ _)).map .instance)
    | 0x3f => some (resourceBodyG.map fun p => .resource p.1 p.2)
    | _ => (defValTypeBody b).map (Grammar.map .val)

theorem defTypeG_nonEmpty (k : Nat) : NonEmpty (defTypeG k).G := by
  cases k with
  | zero => intro _ _ h; exact h.elim
  | succ k => exact tagged_nonEmpty _ _

/-! ### Canonical definitions, start, exports, values -/

def canonOptG : Grammar CanonOpt := tagged "canonopt" fun b => match b.toNat with
  | 0x00 => tag0 .utf8 | 0x01 => tag0 .utf16 | 0x02 => tag0 .latin1utf16
  | 0x03 => some (u32.map .memory) | 0x04 => some (u32.map .realloc)
  | 0x05 => some (u32.map .postReturn) | 0x06 => tag0 .async
  | 0x07 => some (u32.map .callback) | _ => none

def canonOptsG : Grammar (List CanonOpt) := vec canonOptG (tagged_nonEmpty _ _)

def canonG : Grammar Canon := tagged "canon" fun b => match b.toNat with
  | 0x00 => some ((expect "canon lift" 0x00).then_
      (((u32.seq canonOptsG).seq u32).map fun p => .lift p.1.1 p.1.2 p.2))
  | 0x01 => some ((expect "canon lower" 0x00).then_
      ((u32.seq canonOptsG).map fun p => .lower p.1 p.2))
  | 0x02 => some (u32.map .resourceNew)
  | 0x03 => some (u32.map .resourceDrop)
  | 0x04 => some (u32.map .resourceRep)
  | _ => none

def startG : Grammar Start :=
  ((u32.seq (vec u32 u32_nonEmpty)).seq u32).map fun p => ⟨p.1.1, p.1.2, p.2⟩

def exportG : Grammar Export :=
  ((externNameG.seq sortIdxG).seq (opt "export type" externDescG)).map
    fun p => ⟨p.1.1, p.1.2, p.2⟩

def valueG : Grammar Value :=
  (valTypeG.seq (u32.bind fun n => bytes n)).map fun p => ⟨p.1, p.2⟩

/-! ### Sections and components -/

/-- A size-prefixed `vec` section body. -/
@[inline] def vecSection {α β : Type} (g : Grammar α) (hne : NonEmpty g.G) (f : List α → β) :
    Option (Grammar β) := some ((sizedBy (vec g hne)).map f)

/-- Sections, given the grammar of nested components and of type definitions. -/
def sectionG (c : GrammarE Ast) (t : Grammar DefType) (ht : NonEmpty t.G) : Grammar Section :=
  tagged "section" fun b => match b.toNat with
  | 0x00 => some (GrammarE.sizedBy (GrammarE.after name fun n => GrammarE.rest.map (.custom n)))
  | 0x01 => some (GrammarE.sizedBy (GrammarE.rest.map .coreModule))
  | 0x02 => vecSection coreInstanceExprG (tagged_nonEmpty _ _) .coreInstances
  | 0x03 => vecSection coreTypeG coreTypeG_nonEmpty .coreTypes
  | 0x04 => some (GrammarE.sizedBy (c.map .component))
  | 0x05 => vecSection instanceExprG (tagged_nonEmpty _ _) .instances
  | 0x06 => vecSection aliasG aliasG_nonEmpty .aliases
  | 0x07 => vecSection t ht .types
  | 0x08 => vecSection canonG (tagged_nonEmpty _ _) .canons
  | 0x09 => some ((sizedBy startG).map .start)
  | 0x0a => vecSection importG (map_nonEmpty (seq_nonEmpty externNameG_nonEmpty)) .imports
  | 0x0b => vecSection exportG (map_nonEmpty (seq_nonEmpty (seq_nonEmpty externNameG_nonEmpty)))
      .exports
  | 0x0c => vecSection valueG (map_nonEmpty (seq_nonEmpty valTypeG_nonEmpty)) .values
  | _ => none

/-- A component (preamble and sections to the end of the window), nested at
most `k` deep; type definitions at most `k` deep. -/
def componentG : Nat → GrammarE Ast
  | 0 => GrammarE.ofGrammar fail
  | k + 1 => GrammarE.after (lit preambleBytes) fun _ =>
      (GrammarE.items (sectionG (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _))
        (tagged_nonEmpty _ _)).map
        .mk

end Grammar

/-! ## Entry point -/

/-- Parse a component binary. Nesting depth is bounded by the input size,
which every nesting level consumes at least a byte of. -/
def parse (bs : ByteArray) : Except Error Ast :=
  runAll (componentG (bs.size + 1)).parse bs

end Silmaril.Wasm.Component.Binary
