module

public import Silmaril.Wasm.Component.Binary.Defs
public import Silmaril.Wasm.Component.BinaryP3.Defs
public import Silmaril.Wasm.Component.Conformance.ToRef.Defs

/-!
# Component binaries with WebAssembly 3.0 core types and wasmtime's 🛸 GC options

`BinaryP3` (component-model `Binary.md` at `d095e2f`) reuses `Silmaril.Wasm.Component.Binary`'s
core types: function types over the WebAssembly 1.0/2.0 value types, and module types of
them. `Binary.md` defines `core:type` by the WebAssembly 3.0 binary format (`core:rectype`,
with a non-final sub type written `0x00 0x50` in a component core type section, since a bare
`0x50` is a `core:moduletype`). This module reads that grammar, with results in silmaril's
WebAssembly syntax (the reference AST's core types):

* `heapTypeG` (an abstract heap type byte `0x69`-`0x74`, or a non-negative `s33` type index,
  told apart by one byte of lookahead, as wasmparser does), `refTypeG`, `valTypeG`,
  `storageTypeG`, `fieldTypeG`, `compTypeG` (array, struct, func), `subTypeG`, `recTypeG`,
  `limitsG` (32- and 🐘 64-bit), `externTypeG`, `moduleDeclG`, `coreDefTypeG`;
* `defTypeG`: component type definitions whose component and instance type declarators may
  hold such core types (`instancedecl ::= 0x00 core:type`), as reference syntax;
* `canonOptG`: `Binary.md`'s options and wasmtime's 🛸 `0x08 core-type` and `0x09 gc` (GC
  canonical ABI; not in `Binary.md` at `d095e2f`; checked against `wasm-tools dump` 1.262.0),
  allowed on `lift` and `lower` (`canonG`: one byte of lookahead between those two and every
  other `BinaryP3` built-in);
* `sectionG`, `componentG`, `parse`: `BinaryP3`'s, with those three sections replaced.

Every grammar is built from the verified combinators of `Silmaril.Parse.ByteParse`, so `parse` is
sound and complete for `componentG` by construction. `componentG` does not include
`BinaryP3.componentG` (a resource represented as `f32` is in the latter only:
`Codec.not_lax_sub_gc`; the runner only uses this grammar where `BinaryP3` fails,
`Conformance.DecodeGC`). Not proved: an encoder and round trip, and agreement with
silmaril's grammar `Silmaril.Wasm.Binary.RecType` (shared sub types `0x65`, exact and
descriptor types of later proposals are not read).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryGC

open Silmaril.Parse.ByteParse (Grammar GrammarE NonEmpty Bytes StartsWith)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Component.Binary (tag0)
open Silmaril.Wasm.Component

/-! ## Core types of WebAssembly 3.0 (results in silmaril's syntax) -/

/-- An abstract heap type byte (`0x69`-`0x74`). -/
def absHeap? (b : UInt8) : Option Silmaril.Wasm.AbsHeapType := match b.toNat with
  | 0x69 => some .exn | 0x6a => some .array | 0x6b => some .struct | 0x6c => some .i31
  | 0x6d => some .eq | 0x6e => some .any | 0x6f => some .extern | 0x70 => some .func
  | 0x71 => some .none | 0x72 => some .noextern | 0x73 => some .nofunc | 0x74 => some .noexn
  | _ => none

theorem absHeap?_range (b : UInt8) (h : (absHeap? b).isSome) :
    (0x40 ≤ b && b < 0x80) = true := by
  revert b; decide

def absHeapG : Grammar Silmaril.Wasm.AbsHeapType := tagged "absheaptype" fun b =>
  (absHeap? b).map Grammar.pure

/-- A type index: `u32`, below `2 ^ 32`. -/
def typeIdx? (n : Nat) : Option Silmaril.Wasm.TypeIdx :=
  if h : n < 2 ^ 32 then some ⟨⟨n, h⟩⟩ else none

def typeIdxG : Grammar Silmaril.Wasm.TypeIdx := u32.filterMap "type index" typeIdx?

/-- A type index as a non-negative `s33` (`heaptype`). -/
def heapIdx? (i : Int) : Option Silmaril.Wasm.HeapType :=
  if 0 ≤ i then (typeIdx? i.toNat).map .typeIdx else none

def heapIdxG : Grammar Silmaril.Wasm.HeapType := (sN 33).filterMap "heap type index" heapIdx?

theorem absHeapG_starts :
    StartsWith (fun b => (0x40 ≤ b && b < 0x80) = true)
      (absHeapG.map Silmaril.Wasm.HeapType.abstract).G := by
  rintro l _ ⟨a, ⟨b, l', G, rfl, hK, -⟩, -⟩
  refine ⟨b, l', rfl, absHeap?_range b ?_⟩
  cases h : absHeap? b <;> simp_all

theorem heapIdxG_starts :
    StartsWith (fun b => (0x40 ≤ b && b < 0x80) = false) heapIdxG.G := by
  rintro l a ⟨i, hi, hf⟩
  cases hi with
  | pos n h₁ h₂ => exact ⟨n, [], rfl, by simp [UInt8.le_iff_toNat_le]; omega⟩
  | neg n h₁ h₂ h₃ =>
    exfalso
    simp only [heapIdx?] at hf
    split at hf
    · omega
    · cases hf
  | cont n h₁ h₂ rest => exact ⟨n, _, rfl, by simp [UInt8.lt_iff_toNat_lt]; omega⟩

/-- `heaptype`: an abstract heap type byte, or a non-negative `s33` type index. -/
def heapTypeG : Grammar Silmaril.Wasm.HeapType :=
  choice (fun b => 0x40 ≤ b && b < 0x80) (absHeapG.map Silmaril.Wasm.HeapType.abstract) heapIdxG
    absHeapG_starts
    heapIdxG_starts

/-- The branch of a reference type after its first byte. -/
def refBody (b : UInt8) : Option (Grammar Silmaril.Wasm.RefType) :=
  match b.toNat with
  | 0x63 => some (heapTypeG.map fun h => ⟨true, h⟩)
  | 0x64 => some (heapTypeG.map fun h => ⟨false, h⟩)
  | _ => (absHeap? b).map fun a => Grammar.pure ⟨true, .abstract a⟩

def refTypeG : Grammar Silmaril.Wasm.RefType := tagged "reftype" refBody

/-- The branch of a value type after its first byte. -/
def valBody (b : UInt8) : Option (Grammar Silmaril.Wasm.ValType) :=
  match b.toNat with
  | 0x7f => tag0 (.num (.int .i32))
  | 0x7e => tag0 (.num (.int .i64))
  | 0x7d => tag0 (.num (.float .f32))
  | 0x7c => tag0 (.num (.float .f64))
  | 0x7b => tag0 (.vec .v128)
  | _ => (refBody b).map (Grammar.map .ref)

def valTypeG : Grammar Silmaril.Wasm.ValType := tagged "valtype" valBody

theorem valTypeG_nonEmpty : NonEmpty valTypeG.G := tagged_nonEmpty _ _

def mutG : Grammar Silmaril.Wasm.Mutability := tagged "mut" fun b => match b.toNat with
  | 0x00 => tag0 .const | 0x01 => tag0 .var | _ => none

def storageTypeG : Grammar Silmaril.Wasm.StorageType := tagged "storagetype" fun b =>
  match b.toNat with
  | 0x78 => tag0 (.packed .i8)
  | 0x77 => tag0 (.packed .i16)
  | _ => (valBody b).map (Grammar.map .val)

def fieldTypeG : Grammar Silmaril.Wasm.FieldType :=
  (storageTypeG.seq mutG).map fun p => ⟨p.2, p.1⟩

theorem fieldTypeG_nonEmpty : NonEmpty fieldTypeG.G :=
  map_nonEmpty (seq_nonEmpty (tagged_nonEmpty _ _))

/-- The branch of a composite type after its first byte. -/
def compBody (b : UInt8) : Option (Grammar Silmaril.Wasm.CompositeType) :=
  match b.toNat with
  | 0x5e => some (fieldTypeG.map .array)
  | 0x5f => some ((vec fieldTypeG fieldTypeG_nonEmpty).map .struct)
  | 0x60 => some (((vec valTypeG valTypeG_nonEmpty).seq (vec valTypeG valTypeG_nonEmpty)).map
      fun p => .func ⟨p.1, p.2⟩)
  | _ => none

def compTypeG : Grammar Silmaril.Wasm.CompositeType := tagged "comptype" compBody

def typeIdxs : Grammar (List Silmaril.Wasm.TypeIdx) :=
  vec typeIdxG (filterMap_nonEmpty u32_nonEmpty)

/-- The branch of a sub type after its first byte. -/
def subBody (b : UInt8) : Option (Grammar Silmaril.Wasm.SubType) :=
  match b.toNat with
  | 0x50 => some ((typeIdxs.seq compTypeG).map fun p => ⟨false, p.1, p.2⟩)
  | 0x4f => some ((typeIdxs.seq compTypeG).map fun p => ⟨true, p.1, p.2⟩)
  | _ => (compBody b).map (Grammar.map fun ct => ⟨true, [], ct⟩)

def subTypeG : Grammar Silmaril.Wasm.SubType := tagged "subtype" subBody

/-- The branch of a recursive type after its first byte. -/
def recBody (b : UInt8) : Option (Grammar Silmaril.Wasm.RecType) :=
  match b.toNat with
  | 0x4e => some ((vec subTypeG (tagged_nonEmpty _ _)).map fun sts => ⟨sts⟩)
  | _ => (subBody b).map (Grammar.map fun st => ⟨[st]⟩)

def recTypeG : Grammar Silmaril.Wasm.RecType := tagged "rectype" recBody

/-- `limits`: `0x00`/`0x01` with `u32` bounds (32-bit), `0x04`/`0x05` with `u64` bounds
(🐘 64-bit). -/
def limitsG : Grammar (Silmaril.Wasm.AddrType × Silmaril.Wasm.Limits) :=
  let b64 (n : Nat) : Option (Fin (2 ^ 64)) := if h : n < 2 ^ 64 then some ⟨n, h⟩ else none
  tagged "limits" fun b => match b.toNat with
  | 0x00 => some (u32.filterMap "limit" fun n => (b64 n).map fun m => (.i32, ⟨m, none⟩))
  | 0x01 => some ((u32.seq u32).filterMap "limit" fun p => do
      pure (.i32, ⟨← b64 p.1, some (← b64 p.2)⟩))
  | 0x04 => some ((uN 64).filterMap "limit" fun n => (b64 n).map fun m => (.i64, ⟨m, none⟩))
  | 0x05 => some (((uN 64).seq (uN 64)).filterMap "limit" fun p => do
      pure (.i64, ⟨← b64 p.1, some (← b64 p.2)⟩))
  | _ => none

/-- `core:externtype` (`core:importdesc`). -/
def externTypeG : Grammar Silmaril.Wasm.ExternType := tagged "externtype" fun b =>
  match b.toNat with
  | 0x00 => some (typeIdxG.map .func)
  | 0x01 => some ((refTypeG.seq limitsG).map fun p => .table ⟨p.2.1, p.2.2, p.1⟩)
  | 0x02 => some (limitsG.map fun p => .memory ⟨p.1, p.2⟩)
  | 0x03 => some ((valTypeG.seq mutG).map fun p => .global ⟨p.2, p.1⟩)
  | 0x04 => some ((expect "tag attribute" 0x00).then_ (typeIdxG.map .tag))
  | _ => none

/-- `core:moduledecl`: type declarators carry a `core:rectype` (a bare `0x50` is a non-final
sub type here). -/
def moduleDeclG : Grammar Syntax.CoreModuleDecl := tagged "core:moduledecl" fun b =>
  match b.toNat with
  | 0x00 => some (((name.seq name).seq externTypeG).map fun p => .import_ p.1.1 p.1.2 p.2)
  | 0x01 => some (recTypeG.map .type)
  | 0x02 => some ((lit [0x10, 0x01]).then_ ((u32.seq u32).map fun p => .aliasOuter p.1 p.2))
  | 0x03 => some ((name.seq externTypeG).map fun p => .export_ p.1 p.2)
  | _ => none

/-- `core:type` of a component core type section (`core:deftype`): a `core:rectype` except
that a non-final sub type is written `0x00 0x50` (a bare `0x50` is a `core:moduletype`). -/
def coreDefTypeG : Grammar Syntax.CoreTypeDef := tagged "core:type" fun b =>
  match b.toNat with
  | 0x00 => some ((expect "core:subtype" 0x50).then_
      ((typeIdxs.seq compTypeG).map fun p => .rec_ ⟨[⟨false, p.1, p.2⟩]⟩))
  | 0x50 => some ((vec moduleDeclG (tagged_nonEmpty _ _)).map .module_)
  | _ => if b.toNat = 0x50 then none else (recBody b).map (Grammar.map .rec_)

theorem coreDefTypeG_nonEmpty : NonEmpty coreDefTypeG.G := tagged_nonEmpty _ _

/-! ## Canonical options with wasmtime's 🛸 GC options -/

/-- `canonopt`: `Binary.md`'s (`v0`), and wasmtime's 🛸 `core-type` (`0x08 t`) and `gc`
(`0x09`) of the GC canonical ABI (not in `Binary.md` at `d095e2f`). -/
inductive CanonOpt where
  | v0 (o : Binary.CanonOpt)
  | coreType (t : Nat)
  | gc
  deriving Repr, DecidableEq, Inhabited

def canonOptG : Grammar CanonOpt := tagged "canonopt" fun b => match b.toNat with
  | 0x00 => tag0 (.v0 .utf8) | 0x01 => tag0 (.v0 .utf16) | 0x02 => tag0 (.v0 .latin1utf16)
  | 0x03 => some (u32.map fun i => .v0 (.memory i))
  | 0x04 => some (u32.map fun i => .v0 (.realloc i))
  | 0x05 => some (u32.map fun i => .v0 (.postReturn i))
  | 0x06 => tag0 (.v0 .async)
  | 0x07 => some (u32.map fun i => .v0 (.callback i))
  | 0x08 => some (u32.map .coreType)
  | 0x09 => tag0 .gc
  | _ => none

def canonOptsG : Grammar (List CanonOpt) := vec canonOptG (tagged_nonEmpty _ _)

/-- A built-in: `canon lift`/`lower` with the options above, or any other `BinaryP3` one. -/
inductive Canon where
  | lift (coreFunc : Nat) (opts : List CanonOpt) (type : Nat)
  | lower (func : Nat) (opts : List CanonOpt)
  | p3 (c : BinaryP3.Canon)
  deriving Repr, DecidableEq, Inhabited

/-- The branches of `lift` and `lower` (tags `0x00`, `0x01`) with the extended options. -/
def liftLowerK (b : UInt8) : Option (Grammar Canon) := match b.toNat with
  | 0x00 => some ((expect "canon lift" 0x00).then_
      (((u32.seq canonOptsG).seq u32).map fun p => .lift p.1.1 p.1.2 p.2))
  | 0x01 => some ((expect "canon lower" 0x00).then_
      ((u32.seq canonOptsG).map fun p => .lower p.1 p.2))
  | _ => none

def liftLowerG : Grammar Canon := tagged "canon" liftLowerK

/-- The other built-ins: `BinaryP3.canonG` without `lift` and `lower`. -/
def otherOf? : BinaryP3.Canon → Option Canon
  | .lift .. | .lower .. => none
  | c => some (.p3 c)

def otherG : Grammar Canon := BinaryP3.canonG.filterMap "canon" otherOf?

/-- Is the first byte a `lift`/`lower` tag. -/
def isLiftLower (b : UInt8) : Bool := b == 0x00 || b == 0x01

theorem liftLowerK_isSome : ∀ b, (liftLowerK b).isSome = true → isLiftLower b = true := by
  decide

theorem liftLowerG_starts : StartsWith (fun b => isLiftLower b = true) liftLowerG.G := by
  rintro l a ⟨b, l', G, rfl, hK, -⟩
  refine ⟨b, l', rfl, liftLowerK_isSome b ?_⟩
  cases h : liftLowerK b <;> simp_all

/-- A `BinaryP3` built-in read after tag `0x00`/`0x01` is a `lift`/`lower`. -/
theorem canonG_liftLower {b : UInt8} {l : Bytes} {c : BinaryP3.Canon}
    (hb : isLiftLower b = true) (h : BinaryP3.canonG.G (b :: l) c) : otherOf? c = none := by
  obtain ⟨b', l', G, he, hK, hG⟩ := h
  obtain ⟨rfl, rfl⟩ := List.cons.inj he
  have hb' : b = 0x00 ∨ b = 0x01 := by simpa [isLiftLower] using hb
  rcases hb' with rfl | rfl
  · obtain ⟨_, _, _, -, -, ⟨q, -, rfl⟩⟩ : (((expect "canon lift" 0x00).then_
        (((u32.seq Binary.canonOptsG).seq u32).map fun p =>
          BinaryP3.Canon.lift p.1.1 p.1.2 p.2))).G l c := by
      have hK' : some (Grammar.G _) = some G := hK
      exact (Option.some.inj hK') ▸ hG
    rfl
  · obtain ⟨_, _, _, -, -, ⟨q, -, rfl⟩⟩ : (((expect "canon lower" 0x00).then_
        ((u32.seq Binary.canonOptsG).map fun p => BinaryP3.Canon.lower p.1 p.2))).G l c := by
      have hK' : some (Grammar.G _) = some G := hK
      exact (Option.some.inj hK') ▸ hG
    rfl

theorem otherG_starts : StartsWith (fun b => isLiftLower b = false) otherG.G := by
  rintro l x ⟨c, hc, hf⟩
  obtain ⟨b, l', rfl⟩ : ∃ b l', l = b :: l' := by
    cases l with
    | nil => exact absurd rfl (BinaryP3.canonG_nonEmpty hc)
    | cons b l' => exact ⟨b, l', rfl⟩
  refine ⟨b, l', rfl, ?_⟩
  cases hb : isLiftLower b
  · exact hb
  · rw [canonG_liftLower hb hc] at hf
    cases hf

def canonG : Grammar Canon :=
  choice isLiftLower liftLowerG otherG liftLowerG_starts otherG_starts

theorem canonG_nonEmpty : NonEmpty canonG.G := choice_nonEmpty

/-! ## Type definitions with WebAssembly 3.0 core types in their declarators

A component or instance type declares core types (`instancedecl ::= 0x00 core:type`), so a
type section needs `coreDefTypeG` there too. Its results are reference syntax
(`Syntax.DefType`) directly, with the maps of `Conformance.ToRef`; a declarator `ToRef`
rejects (a non-core sort in a core export alias, a resource representation other than
`i32`/`i64`) is rejected by the grammar (`filterMap`). -/

section Types
open Silmaril.Wasm.Component.Binary (aliasG externNameG externDescG defValTypeBody funcTypeBodyG
  resourceBodyG)
open Silmaril.Wasm.Component.Conformance (ToRef.aliasDef ToRef.externName ToRef.externDesc
  ToRef.funcType ToRef.defValType ToRef.addrType)

def instanceDeclBody (t : Grammar Syntax.DefType) (b : UInt8) :
    Option (Grammar Syntax.InstanceDecl) :=
  match b.toNat with
  | 0x00 => some (coreDefTypeG.map .coreType)
  | 0x01 => some (t.map .type)
  | 0x02 => some (aliasG.filterMap "alias" fun a => (ToRef.aliasDef a).toOption.map .alias)
  | 0x04 => some ((externNameG.seq externDescG).map fun p =>
      .export_ (ToRef.externName p.1) (ToRef.externDesc p.2))
  | _ => none

def componentDeclBody (t : Grammar Syntax.DefType) (b : UInt8) :
    Option (Grammar Syntax.ComponentDecl) :=
  if b.toNat = 0x03 then
    some ((externNameG.seq externDescG).map fun p =>
      .import_ (ToRef.externName p.1) (ToRef.externDesc p.2))
  else (instanceDeclBody t b).map (Grammar.map .decl)

/-- `deftype`, nested at most `k` deep, as reference syntax. -/
def defTypeG : Nat → Grammar Syntax.DefType
  | 0 => fail
  | k + 1 => tagged "type" fun b => match b.toNat with
    | 0x40 => some ((funcTypeBodyG false).map fun f => .func (ToRef.funcType f))
    | 0x43 => some ((funcTypeBodyG true).map fun f => .func (ToRef.funcType f))
    | 0x41 => some ((vec (tagged "componentdecl" (componentDeclBody (defTypeG k)))
        (tagged_nonEmpty _ _)).map .component)
    | 0x42 => some ((vec (tagged "instancedecl" (instanceDeclBody (defTypeG k)))
        (tagged_nonEmpty _ _)).map .instance_)
    | 0x3f => some (resourceBodyG.filterMap "resource" fun p =>
        (ToRef.addrType p.1).toOption.map fun r => .resource r p.2)
    | _ => (defValTypeBody b).map (Grammar.map fun d => .val (ToRef.defValType d))

theorem defTypeG_nonEmpty (k : Nat) : NonEmpty (defTypeG k).G := by
  cases k with
  | zero => intro _ _ h; exact h.elim
  | succ k => exact tagged_nonEmpty _ _

end Types

/-! ## Sections and components -/

mutual
/-- Sections: a `BinaryP3` section, or one of the three this grammar reads differently. -/
inductive Section where
  | p3 (s : BinaryP3.Section)
  | coreTypes (xs : List Syntax.CoreTypeDef)
  | types (xs : List Syntax.DefType)
  | canons (xs : List Canon)
  | component (c : Ast)
/-- A component: its sections in order. -/
inductive Ast where
  | mk (sections : List Section)
end

instance : Inhabited Ast := ⟨.mk []⟩

section Grammar
open Silmaril.Wasm.Component.Binary (coreInstanceExprG instanceExprG aliasG aliasG_nonEmpty startG
  importG externNameG_nonEmpty exportG valueG preambleBytes vecSection)

/-- Sections: core type sections with WebAssembly 3.0 types, type sections whose declarators
may hold them (`defTypeG`, reference syntax), canon sections with the extended options,
nested components; every other section as `BinaryP3.sectionG` reads it. -/
def sectionG (c : GrammarE Ast) (t : Grammar Syntax.DefType) (ht : NonEmpty t.G) :
    Grammar Section :=
  tagged "section" fun b => match b.toNat with
  | 0x00 => some (GrammarE.sizedBy (GrammarE.after name fun n =>
      GrammarE.rest.map fun d => .p3 (.custom n d)))
  | 0x01 => some (GrammarE.sizedBy (GrammarE.rest.map fun d => .p3 (.coreModule d)))
  | 0x02 => vecSection coreInstanceExprG (tagged_nonEmpty _ _) (.p3 ∘ .coreInstances)
  | 0x03 => vecSection coreDefTypeG coreDefTypeG_nonEmpty .coreTypes
  | 0x04 => some (GrammarE.sizedBy (c.map .component))
  | 0x05 => vecSection instanceExprG (tagged_nonEmpty _ _) (.p3 ∘ .instances)
  | 0x06 => vecSection aliasG aliasG_nonEmpty (.p3 ∘ .aliases)
  | 0x07 => vecSection t ht .types
  | 0x08 => vecSection canonG canonG_nonEmpty .canons
  | 0x09 => some ((sizedBy startG).map (.p3 ∘ .start))
  | 0x0a => vecSection importG (map_nonEmpty (seq_nonEmpty externNameG_nonEmpty))
      (.p3 ∘ .imports)
  | 0x0b => vecSection exportG (map_nonEmpty (seq_nonEmpty (seq_nonEmpty externNameG_nonEmpty)))
      (.p3 ∘ .exports)
  | 0x0c => vecSection valueG (map_nonEmpty (seq_nonEmpty Binary.valTypeG_nonEmpty)) (.p3 ∘ .values)
  | _ => none

/-- A component nested at most `k` deep (as `BinaryP3.componentG`). -/
def componentG : Nat → GrammarE Ast
  | 0 => GrammarE.ofGrammar fail
  | k + 1 => GrammarE.after (lit preambleBytes) fun _ =>
      (GrammarE.items (sectionG (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _))
        (tagged_nonEmpty _ _)).map .mk

end Grammar

/-- Parse a component binary with WebAssembly 3.0 core types and the 🛸 options. -/
def parse (bs : ByteArray) : Except Silmaril.Parse.ByteParse.Error Ast :=
  Silmaril.Parse.ByteParse.runAll (componentG (bs.size + 1)).parse bs

end Silmaril.Wasm.Component.BinaryGC
