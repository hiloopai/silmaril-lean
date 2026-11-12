module

public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.JcoTool.Emit.Defs

/-!
# Component binaries with the async canonical built-ins

The verified component grammar of `Silmaril.Wasm.Component.Binary` covers `canon lift`,
`canon lower` and the resource built-ins, and reports the async built-ins of the Canonical ABI
(`task.return`, `stream.*`, `future.*`, `waitable-set.*`, …) as unknown `canon` tags. This
module extends it without changing it:

* `CanonX`: a `canon` of the base grammar or a built-in (`JcoTool.Builtin`, the built-ins
  `wasm-jco` writes, with the opcodes of `Binary.md` checked against `wasm-tools dump`);
* `SectionX`, `AstX`: the sections and components of the base grammar, with `canon`
  sections of `CanonX` (and nested components of `AstX`);
* `canonXG`, `sectionXG`, `componentXG`: the grammar, from the verified combinators of
  `Silmaril.Parse.ByteParse` and the productions of the base grammar; `parseX` its parser;
* `EncodeX`: the encoder, the base encoder on every production but `canon`;
* `AstX.ofAst` (a base component is an extended one) and `AstX.erase` (forget the
  built-ins, keeping every other definition in order).

The built-ins define *core* functions only. Everything the component-level type of a binary
depends on (imports, exports, types, instances, aliases, `canon lift`) is unchanged by
`erase`, which is how `Silmaril.Wasm.Wac.TypeOfX` infers the type of a stream component.

Theorems (`Silmaril.Wasm.Component.BinaryAsync.Thms`): `parseX_encodeX` (round trip),
`parseX_sound`, `componentXG_functional`, `encodeX_ofAst` (on base components the encoder is
the base encoder), `erase_ofAst`, and `parseX_xast` (the bytes `wasm-jco` writes with
built-ins parse back).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryAsync

open Silmaril.Parse.ByteParse (Grammar GrammarE NonEmpty Bytes Error runAll)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.JcoTool (Builtin XAst XSection)

/-! ## Abstract syntax -/

/-- The built-ins of `Binary.md` outside `JcoTool.Builtin` (which `wasm-jco` does not write):
the thread built-ins (🧵), `stream.forward`/`future.forward`, and the async `resource.drop`.
Opcodes and operands as wasm-tools 1.262.0 reads them (`wasm-tools dump`, recorded in
`docs/projects/wasm-components.md`): the four `thread.*-then-*` and `thread.suspend` carry a zero
byte (formerly the `cancellable` flag). wasm-tools 1.262.0 rejects `0x07` (async
`resource.drop`, "invalid leading byte"); it is kept here as `Binary.md` lists it. -/
inductive ExtraBuiltin where
  | resourceDropAsync (t : Nat)
  | threadIndex
  | threadNewIndirect (ft tbl : Nat)
  | threadResumeLater
  | threadSuspend
  | threadSuspendThenResume
  | threadYieldThenResume
  | threadSuspendThenPromote
  | threadYieldThenPromote
  | streamForward (t : Nat)
  | futureForward (t : Nat)
  | threadSpawnRef (ft : Nat)
  | threadSpawnIndirect (ft tbl : Nat)
  | threadAvailableParallelism
  deriving Repr, DecidableEq, Inhabited

namespace ExtraBuiltin

open Silmaril.Parse.ByteParse.Enc (u32)

/-- An opcode followed by two `u32`s. -/
def withTT (op : UInt8) (a b : Nat) : Option Bytes := do
  let x ← u32 a
  let y ← u32 b
  pure (op :: (x ++ y))

/-- The bytes of a built-in. -/
def encode : ExtraBuiltin → Option Bytes
  | .resourceDropAsync t => Builtin.withT 0x07 t
  | .threadIndex => some [0x26]
  | .threadNewIndirect f t => withTT 0x27 f t
  | .threadResumeLater => some [0x28]
  | .threadSuspend => some [0x29, 0x00]
  | .threadSuspendThenResume => some [0x2a, 0x00]
  | .threadYieldThenResume => some [0x2b, 0x00]
  | .threadSuspendThenPromote => some [0x2c, 0x00]
  | .threadYieldThenPromote => some [0x2d, 0x00]
  | .streamForward t => Builtin.withT 0x2e t
  | .futureForward t => Builtin.withT 0x2f t
  | .threadSpawnRef f => Builtin.withT 0x40 f
  | .threadSpawnIndirect f t => withTT 0x41 f t
  | .threadAvailableParallelism => some [0x42]

end ExtraBuiltin

/-- A `canon` definition: one of the base grammar, an async built-in of `wasm-jco`, or one of
the other built-ins (`ExtraBuiltin`). -/
inductive CanonX where
  | base (c : Canon)
  | builtin (b : Builtin)
  | extra (e : ExtraBuiltin)
  deriving Repr, DecidableEq, Inhabited

mutual
/-- A section of an extended component. -/
inductive SectionX where
  | custom (name : String) (data : ByteArray)
  | coreModule (bytes : ByteArray)
  | coreInstances (xs : List CoreInstanceExpr)
  | coreTypes (xs : List CoreType)
  | component (c : AstX)
  | instances (xs : List InstanceExpr)
  | aliases (xs : List Alias)
  | types (xs : List DefType)
  | canons (xs : List CanonX)
  | start (s : Start)
  | imports (xs : List Import)
  | exports (xs : List Export)
  | values (xs : List Value)

/-- An extended component: its sections in order. -/
inductive AstX where
  | mk (sections : List SectionX)
end

def AstX.sections : AstX → List SectionX | .mk ss => ss

instance : Inhabited AstX := ⟨.mk []⟩

/-! ## Grammar -/

section Grammar
open Silmaril.Parse.ByteParse.Grammar

/-- A built-in written as its opcode and a zero byte. -/
@[inline] def zero0 (x : CanonX) : Option (Grammar CanonX) :=
  some ((expect "zero byte" 0x00).then_ (Grammar.pure x))

/-- The body of a built-in or base `canon`, after its tag. -/
def canonXBody (b : UInt8) : Option (Grammar CanonX) :=
  match b.toNat with
  | 0x00 => some ((expect "canon lift" 0x00).then_
      (((u32.seq canonOptsG).seq u32).map fun p => .base (.lift p.1.1 p.1.2 p.2)))
  | 0x01 => some ((expect "canon lower" 0x00).then_
      ((u32.seq canonOptsG).map fun p => .base (.lower p.1 p.2)))
  | 0x02 => some (u32.map fun t => .base (.resourceNew t))
  | 0x03 => some (u32.map fun t => .base (.resourceDrop t))
  | 0x04 => some (u32.map fun t => .base (.resourceRep t))
  | 0x05 => tag0 (.builtin .taskCancel)
  | 0x06 => some (mutG.map fun a => .builtin (.subtaskCancel a))
  | 0x09 => some ((resultListG.seq canonOptsG).map fun p => .builtin (.taskReturn p.1 p.2))
  | 0x0a => some ((expect "context type" 0x7f).then_ (u32.map fun i => .builtin (.contextGet i)))
  | 0x0b => some ((expect "context type" 0x7f).then_ (u32.map fun i => .builtin (.contextSet i)))
  | 0x0c => some (mutG.map fun c => .builtin (.threadYield c))
  | 0x0d => tag0 (.builtin .subtaskDrop)
  | 0x0e => some (u32.map fun t => .builtin (.streamNew t))
  | 0x0f => some ((u32.seq canonOptsG).map fun p => .builtin (.streamRead p.1 p.2))
  | 0x10 => some ((u32.seq canonOptsG).map fun p => .builtin (.streamWrite p.1 p.2))
  | 0x11 => some ((u32.seq mutG).map fun p => .builtin (.streamCancelRead p.1 p.2))
  | 0x12 => some ((u32.seq mutG).map fun p => .builtin (.streamCancelWrite p.1 p.2))
  | 0x13 => some (u32.map fun t => .builtin (.streamDropReadable t))
  | 0x14 => some (u32.map fun t => .builtin (.streamDropWritable t))
  | 0x15 => some (u32.map fun t => .builtin (.futureNew t))
  | 0x16 => some ((u32.seq canonOptsG).map fun p => .builtin (.futureRead p.1 p.2))
  | 0x17 => some ((u32.seq canonOptsG).map fun p => .builtin (.futureWrite p.1 p.2))
  | 0x18 => some ((u32.seq mutG).map fun p => .builtin (.futureCancelRead p.1 p.2))
  | 0x19 => some ((u32.seq mutG).map fun p => .builtin (.futureCancelWrite p.1 p.2))
  | 0x1a => some (u32.map fun t => .builtin (.futureDropReadable t))
  | 0x1b => some (u32.map fun t => .builtin (.futureDropWritable t))
  | 0x1c => some (canonOptsG.map fun o => .builtin (.errorContextNew o))
  | 0x1d => some (canonOptsG.map fun o => .builtin (.errorContextDebugMessage o))
  | 0x1e => tag0 (.builtin .errorContextDrop)
  | 0x1f => tag0 (.builtin .waitableSetNew)
  | 0x20 => some ((mutG.seq u32).map fun p => .builtin (.waitableSetWait p.1 p.2))
  | 0x21 => some ((mutG.seq u32).map fun p => .builtin (.waitableSetPoll p.1 p.2))
  | 0x22 => tag0 (.builtin .waitableSetDrop)
  | 0x23 => tag0 (.builtin .waitableJoin)
  | 0x24 => tag0 (.builtin .backpressureInc)
  | 0x25 => tag0 (.builtin .backpressureDec)
  | 0x07 => some (u32.map fun t => .extra (.resourceDropAsync t))
  | 0x26 => tag0 (.extra .threadIndex)
  | 0x27 => some ((u32.seq u32).map fun p => .extra (.threadNewIndirect p.1 p.2))
  | 0x28 => tag0 (.extra .threadResumeLater)
  | 0x29 => zero0 (.extra .threadSuspend)
  | 0x2a => zero0 (.extra .threadSuspendThenResume)
  | 0x2b => zero0 (.extra .threadYieldThenResume)
  | 0x2c => zero0 (.extra .threadSuspendThenPromote)
  | 0x2d => zero0 (.extra .threadYieldThenPromote)
  | 0x2e => some (u32.map fun t => .extra (.streamForward t))
  | 0x2f => some (u32.map fun t => .extra (.futureForward t))
  | 0x40 => some (u32.map fun t => .extra (.threadSpawnRef t))
  | 0x41 => some ((u32.seq u32).map fun p => .extra (.threadSpawnIndirect p.1 p.2))
  | 0x42 => tag0 (.extra .threadAvailableParallelism)
  | _ => none

/-- `canon`, with the async built-ins. -/
def canonXG : Grammar CanonX := tagged "canon" canonXBody

/-- A size-prefixed `vec` section body. -/
@[inline] def vecSectionX {α : Type} (g : Grammar α) (hne : NonEmpty g.G) (f : List α → SectionX) :
    Option (Grammar SectionX) := some ((sizedBy (vec g hne)).map f)

/-- Sections, given the grammar of nested components and of type definitions. -/
def sectionXG (c : GrammarE AstX) (t : Grammar DefType) (ht : NonEmpty t.G) : Grammar SectionX :=
  tagged "section" fun b => match b.toNat with
  | 0x00 => some (GrammarE.sizedBy (GrammarE.after name fun n => GrammarE.rest.map (.custom n)))
  | 0x01 => some (GrammarE.sizedBy (GrammarE.rest.map .coreModule))
  | 0x02 => vecSectionX coreInstanceExprG (tagged_nonEmpty _ _) .coreInstances
  | 0x03 => vecSectionX coreTypeG coreTypeG_nonEmpty .coreTypes
  | 0x04 => some (GrammarE.sizedBy (c.map .component))
  | 0x05 => vecSectionX instanceExprG (tagged_nonEmpty _ _) .instances
  | 0x06 => vecSectionX aliasG aliasG_nonEmpty .aliases
  | 0x07 => vecSectionX t ht .types
  | 0x08 => vecSectionX canonXG (tagged_nonEmpty _ _) .canons
  | 0x09 => some ((sizedBy startG).map .start)
  | 0x0a => vecSectionX importG (map_nonEmpty (seq_nonEmpty externNameG_nonEmpty)) .imports
  | 0x0b => vecSectionX exportG (map_nonEmpty (seq_nonEmpty (seq_nonEmpty externNameG_nonEmpty)))
      .exports
  | 0x0c => vecSectionX valueG (map_nonEmpty (seq_nonEmpty valTypeG_nonEmpty)) .values
  | _ => none

/-- An extended component, nested at most `k` deep. -/
def componentXG : Nat → GrammarE AstX
  | 0 => GrammarE.ofGrammar fail
  | k + 1 => GrammarE.after (lit preambleBytes) fun _ =>
      (GrammarE.items (sectionXG (componentXG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _))
        (tagged_nonEmpty _ _)).map
        .mk

end Grammar

/-- **Parse a component binary with the async built-ins.** -/
def parseX (bs : ByteArray) : Except Error AstX :=
  runAll (componentXG (bs.size + 1)).parse bs

/-! ## Encoder -/

namespace EncodeX

/-- A `canon`. -/
def canon : CanonX → Option Bytes
  | .base c => Encode.canon c
  | .builtin b => b.encode
  | .extra e => e.encode

mutual
/-- A section. -/
def section_ : SectionX → Option Bytes
  | .custom n d => Encode.section_ (.custom n d)
  | .coreModule m => Encode.section_ (.coreModule m)
  | .coreInstances xs => Encode.section_ (.coreInstances xs)
  | .coreTypes xs => Encode.section_ (.coreTypes xs)
  | .component c => do
    let b ← ast c
    let s ← Silmaril.Parse.ByteParse.Enc.sized b
    pure (0x04 :: s)
  | .instances xs => Encode.section_ (.instances xs)
  | .aliases xs => Encode.section_ (.aliases xs)
  | .types xs => Encode.section_ (.types xs)
  | .canons xs => Encode.vecSection 0x08 canon xs
  | .start s => Encode.section_ (.start s)
  | .imports xs => Encode.section_ (.imports xs)
  | .exports xs => Encode.section_ (.exports xs)
  | .values xs => Encode.section_ (.values xs)
/-- Sections. -/
def sections : List SectionX → Option Bytes
  | [] => some []
  | s :: ss => do
    let a ← section_ s
    let b ← sections ss
    pure (a ++ b)
/-- A component. -/
def ast : AstX → Option Bytes
  | .mk ss => do
    let b ← sections ss
    pure (preambleBytes ++ b)
end

end EncodeX

/-- The binary of an extended component. -/
def encodeX (c : AstX) : Option ByteArray := (EncodeX.ast c).map fun l => ⟨l.toArray⟩

/-! ## Base components and erasure -/

mutual
/-- A base section as an extended one. -/
def SectionX.ofSection : Section → SectionX
  | .custom n d => .custom n d
  | .coreModule m => .coreModule m
  | .coreInstances xs => .coreInstances xs
  | .coreTypes xs => .coreTypes xs
  | .component c => .component (AstX.ofAst c)
  | .instances xs => .instances xs
  | .aliases xs => .aliases xs
  | .types xs => .types xs
  | .canons xs => .canons (xs.map .base)
  | .start s => .start s
  | .imports xs => .imports xs
  | .exports xs => .exports xs
  | .values xs => .values xs
/-- Base sections as extended ones. -/
def SectionX.ofSections : List Section → List SectionX
  | [] => []
  | s :: ss => SectionX.ofSection s :: SectionX.ofSections ss
/-- **A base component is an extended one.** -/
def AstX.ofAst : Ast → AstX
  | .mk ss => .mk (SectionX.ofSections ss)
end

/-- The base `canon`s of a list (the built-ins dropped). -/
def baseCanons (xs : List CanonX) : List Canon :=
  xs.filterMap fun | .base c => some c | _ => none

mutual
/-- Forget the built-ins of a section. -/
def SectionX.erase : SectionX → Section
  | .custom n d => .custom n d
  | .coreModule m => .coreModule m
  | .coreInstances xs => .coreInstances xs
  | .coreTypes xs => .coreTypes xs
  | .component c => .component (AstX.erase c)
  | .instances xs => .instances xs
  | .aliases xs => .aliases xs
  | .types xs => .types xs
  | .canons xs => .canons (baseCanons xs)
  | .start s => .start s
  | .imports xs => .imports xs
  | .exports xs => .exports xs
  | .values xs => .values xs
/-- Forget the built-ins of sections. -/
def SectionX.eraseAll : List SectionX → List Section
  | [] => []
  | s :: ss => SectionX.erase s :: SectionX.eraseAll ss
/-- **Forget the built-ins** (they define core functions only). -/
def AstX.erase : AstX → Ast
  | .mk ss => .mk (SectionX.eraseAll ss)
end

/-- A section that `wasm-jco` writes, as an extended section. -/
def ofXSection : XSection → SectionX
  | .sec s => SectionX.ofSection s
  | .builtins bs => .canons (bs.map .builtin)

/-- A component that `wasm-jco` writes (`JcoTool.XAst`), as an extended component. -/
def ofXAst (c : XAst) : AstX := .mk (c.sections.map ofXSection)

end Silmaril.Wasm.Component.BinaryAsync
