module

public import Silmaril.Wasm.Component.BinaryGC.Defs

/-!
# Component binaries as wasmparser 1.262.0 reads value imports and exports

`Binary.md` at component-model `d095e2f` writes the bound of a 🪙 value import or export as
`externdesc ::= 0x02 b:valuebound` with `valuebound ::= 0x00 i (eq) | 0x01 t`. wasmparser
1.262.0 (`crates/wasmparser/src/readers/component/imports.rs`, `ComponentTypeRef::from_reader`)
reads `0x02 t:valtype` instead: the value type follows the tag directly, and there is no `eq`
bound for values. `wasm-tools parse` writes that form, so every value import in the wasm-tools
test suite is in it (`values/values.wast`, `values/start.wast`).

This module is `BinaryGC`'s grammar with that production changed (`externDescW`), in
import sections, export sections and the declarators of instance and component types, and
with the shared memory limits of the threads proposal in core types (`limitsG`: flags `0x03`,
`0x07`; the `shared` flag is dropped, since silmaril's `MemoryType` has none, so sharedness is
not compared in subtyping). The
abstract syntax is `BinaryGC.Ast`, with wasmparser's `0x02 t` read as `ValueBound.type t`
(`Binary.md`'s `0x01 t`), so the rest of the pipeline (`toRefGC`, the reference validator) is
unchanged. Every grammar is built from the verified combinators of `Silmaril.Parse.ByteParse`, so
`parse` is sound and complete for `componentG` by construction.

How `Validate.decode` uses it (*the settlement*): a binary is read as wasmparser reads it.
`BinaryP3` (and `BinaryGC`) read the same bytes the same way up to the first value
`externdesc`, so where `BinaryP3` succeeds and its result has no value `externdesc`, this
grammar reads the same component; otherwise the binary is read with this grammar
(`Validate.decode`). A binary in `Binary.md`'s form with a value bound is then rejected, as
wasmparser rejects it. Not proved: that agreement of the grammars before the first value
`externdesc` (it is the argument above, checked by the differential suite).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.BinaryW

open Silmaril.Parse.ByteParse (Grammar GrammarE NonEmpty Bytes)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Binary (tag0 ExternDesc externNameG externNameG_nonEmpty
  typeBoundG valTypeG sortIdxG)
open Silmaril.Wasm.Component

/-- `externdesc` as wasmparser reads it: `0x02 t:valtype` for a value. -/
def externDescW : Grammar ExternDesc := tagged "externdesc" fun b => match b.toNat with
  | 0x00 => some ((expect "core module sort" 0x11).then_ (u32.map .coreModule))
  | 0x01 => some (u32.map .func)
  | 0x02 => some (valTypeG.map fun t => .value (.type t))
  | 0x03 => some (typeBoundG.map .type)
  | 0x04 => some (u32.map .component)
  | 0x05 => some (u32.map .instance)
  | _ => none

/-- `import ::= importname externdesc`. -/
def importW : Grammar Binary.Import := (externNameG.seq externDescW).map fun p => ⟨p.1, p.2⟩

/-- `export ::= exportname sortidx externdesc?`. -/
def exportW : Grammar Binary.Export :=
  ((externNameG.seq sortIdxG).seq (opt "export type" externDescW)).map
    fun p => ⟨p.1.1, p.1.2, p.2⟩

/-! ## Shared memories in core types

wasmparser reads the limits flags of the threads proposal, `0x03` (shared, with a maximum)
and `0x07` (shared, 64-bit, with a maximum), in the core types of component type sections
and type declarators; `BinaryGC.limitsG` has the unshared forms only. Silmaril's
`MemoryType` has no `shared` flag, so the flag is read and dropped (see the module header). -/

section Core
open BinaryGC (refTypeG valTypeG mutG typeIdxG typeIdxs compTypeG recTypeG recBody)

/-- `limits` with the shared forms `0x03` and `0x07`. -/
def limitsG : Grammar (Silmaril.Wasm.AddrType × Silmaril.Wasm.Limits) :=
  let b64 (n : Nat) : Option (Fin (2 ^ 64)) := if h : n < 2 ^ 64 then some ⟨n, h⟩ else none
  tagged "limits" fun b => match b.toNat with
  | 0x00 => some (u32.filterMap "limit" fun n => (b64 n).map fun m => (.i32, ⟨m, none⟩))
  | 0x01 | 0x03 => some ((u32.seq u32).filterMap "limit" fun p => do
      pure (.i32, ⟨← b64 p.1, some (← b64 p.2)⟩))
  | 0x04 => some ((uN 64).filterMap "limit" fun n => (b64 n).map fun m => (.i64, ⟨m, none⟩))
  | 0x05 | 0x07 => some (((uN 64).seq (uN 64)).filterMap "limit" fun p => do
      pure (.i64, ⟨← b64 p.1, some (← b64 p.2)⟩))
  | _ => none

/-- `core:externtype` with `limitsG`. -/
def externTypeG : Grammar Silmaril.Wasm.ExternType := tagged "externtype" fun b =>
  match b.toNat with
  | 0x00 => some (typeIdxG.map .func)
  | 0x01 => some ((refTypeG.seq limitsG).map fun p => .table ⟨p.2.1, p.2.2, p.1⟩)
  | 0x02 => some (limitsG.map fun p => .memory ⟨p.1, p.2⟩)
  | 0x03 => some ((BinaryGC.valTypeG.seq mutG).map fun p => .global ⟨p.2, p.1⟩)
  | 0x04 => some ((expect "tag attribute" 0x00).then_ (typeIdxG.map .tag))
  | _ => none

/-- `core:moduledecl` with `externTypeG`. -/
def moduleDeclG : Grammar Syntax.CoreModuleDecl := tagged "core:moduledecl" fun b =>
  match b.toNat with
  | 0x00 => some (((name.seq name).seq externTypeG).map fun p => .import_ p.1.1 p.1.2 p.2)
  | 0x01 => some (recTypeG.map .type)
  | 0x02 => some ((lit [0x10, 0x01]).then_ ((u32.seq u32).map fun p => .aliasOuter p.1 p.2))
  | 0x03 => some ((name.seq externTypeG).map fun p => .export_ p.1 p.2)
  | _ => none

/-- `core:type` with `moduleDeclG` (`BinaryGC.coreDefTypeG` otherwise). -/
def coreDefTypeG : Grammar Syntax.CoreTypeDef := tagged "core:type" fun b =>
  match b.toNat with
  | 0x00 => some ((expect "core:subtype" 0x50).then_
      ((typeIdxs.seq compTypeG).map fun p => .rec_ ⟨[⟨false, p.1, p.2⟩]⟩))
  | 0x50 => some ((vec moduleDeclG (tagged_nonEmpty _ _)).map .module_)
  | _ => if b.toNat = 0x50 then none else (recBody b).map (Grammar.map .rec_)

theorem coreDefTypeG_nonEmpty : NonEmpty coreDefTypeG.G := tagged_nonEmpty _ _

end Core

section Types
open Silmaril.Wasm.Component.Binary (aliasG defValTypeBody funcTypeBodyG resourceBodyG)
open Silmaril.Wasm.Component.Conformance (ToRef.aliasDef ToRef.externName ToRef.externDesc
  ToRef.funcType ToRef.defValType ToRef.addrType)

/-- `BinaryGC.instanceDeclBody` with `externDescW`. -/
def instanceDeclBody (t : Grammar Syntax.DefType) (b : UInt8) :
    Option (Grammar Syntax.InstanceDecl) :=
  match b.toNat with
  | 0x00 => some (coreDefTypeG.map .coreType)
  | 0x01 => some (t.map .type)
  | 0x02 => some (aliasG.filterMap "alias" fun a => (ToRef.aliasDef a).toOption.map .alias)
  | 0x04 => some ((externNameG.seq externDescW).map fun p =>
      .export_ (ToRef.externName p.1) (ToRef.externDesc p.2))
  | _ => none

/-- `BinaryGC.componentDeclBody` with `externDescW`. -/
def componentDeclBody (t : Grammar Syntax.DefType) (b : UInt8) :
    Option (Grammar Syntax.ComponentDecl) :=
  if b.toNat = 0x03 then
    some ((externNameG.seq externDescW).map fun p =>
      .import_ (ToRef.externName p.1) (ToRef.externDesc p.2))
  else (instanceDeclBody t b).map (Grammar.map .decl)

/-- `deftype`, nested at most `k` deep (`BinaryGC.defTypeG` with `externDescW`). -/
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

section Grammar
open Silmaril.Wasm.Component.Binary (coreInstanceExprG instanceExprG aliasG aliasG_nonEmpty startG
  valueG preambleBytes vecSection)
open BinaryGC (Ast Section)

/-- `BinaryGC.sectionG` with `importW` and `exportW`. -/
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
  | 0x08 => vecSection BinaryGC.canonG BinaryGC.canonG_nonEmpty .canons
  | 0x09 => some ((sizedBy startG).map (.p3 ∘ .start))
  | 0x0a => vecSection importW (map_nonEmpty (seq_nonEmpty externNameG_nonEmpty))
      (.p3 ∘ .imports)
  | 0x0b => vecSection exportW (map_nonEmpty (seq_nonEmpty (seq_nonEmpty externNameG_nonEmpty)))
      (.p3 ∘ .exports)
  | 0x0c => vecSection valueG (map_nonEmpty (seq_nonEmpty Binary.valTypeG_nonEmpty)) (.p3 ∘ .values)
  | _ => none

/-- A component nested at most `k` deep. -/
def componentG : Nat → GrammarE Ast
  | 0 => GrammarE.ofGrammar fail
  | k + 1 => GrammarE.after (lit preambleBytes) fun _ =>
      (GrammarE.items (sectionG (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _))
        (tagged_nonEmpty _ _)).map .mk

end Grammar

/-- Parse a component binary as wasmparser 1.262.0 reads it (value bounds `0x02 t`). -/
def parse (bs : ByteArray) : Except Silmaril.Parse.ByteParse.Error BinaryGC.Ast :=
  Silmaril.Parse.ByteParse.runAll (componentG (bs.size + 1)).parse bs

end Silmaril.Wasm.Tools.Component.BinaryW
