module

public import Silmaril.Wasm.JcoTool.Emit.Defs

/-!
# A verified parser for `wasm-jco`'s output components, async built-ins included

The verified component grammar (`Silmaril.Wasm.Component.Binary`) reports the async built-ins
of the Canonical ABI as unknown `canon` tags, so `Binary.parse` rejects every component with
an async export or a stream. This module extends that grammar by exactly what
`Silmaril.Wasm.JcoTool.Builtin` encodes, with the same verified combinators:

* `xcanonK`: a `canon` item is a definition of the verified grammar (`lift`, `lower`,
  `resource.new/drop/rep`) or one of the built-ins (`task.return`, `stream.read`,
  `waitable-set.wait`, `error-context.new`, …), dispatched on its opcode; the two sets of
  opcodes are disjoint;
* `xsectionK`: a section is a section of the verified grammar, except that a `canon` section
  (id `0x08`) holds `XCanon` items;
* `xparse`: the preamble and sections to the end of the input; nested components are read by
  the verified grammar (`componentG`), which `wasm-jco` never nests built-ins into.

The parsed form is `XComp`: a `canon` section is one `XSec.canons` whatever mix of
definitions and built-ins it holds, so the round trip of `Silmaril.Wasm.JcoTool.XParse.Thms` reads
an output component back as its normal form `XAst.norm` (the empty sections `.sec (.canons [])`
and `.builtins []` have the same bytes, so this is the most a parser can return).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool

open Silmaril.Parse.ByteParse (Grammar GrammarE Bytes Error runAll)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Component.Binary

/-! ## Parsed form -/

/-- An item of a `canon` section. -/
inductive XCanon where
  | canon (c : Canon)
  | builtin (b : Builtin)
  deriving Repr, DecidableEq, Inhabited

/-- A section of a parsed output component. -/
inductive XSec where
  | sec (s : Section)
  | canons (xs : List XCanon)

/-- A parsed output component. -/
structure XComp where
  sections : List XSec

/-- The normal form of an emitted section. -/
def XSection.norm : XSection → XSec
  | .sec (.canons cs) => .canons (cs.map .canon)
  | .sec s => .sec s
  | .builtins bs => .canons (bs.map .builtin)

/-- The normal form of an emitted component. -/
def XAst.norm (c : XAst) : XComp := ⟨c.sections.map XSection.norm⟩

/-- The bytes of an item. -/
def XCanon.encode : XCanon → Option Bytes
  | .canon c => Encode.canon c
  | .builtin b => b.encode

/-- The built-ins of a parsed component, in order. -/
def XComp.builtins (c : XComp) : List Builtin :=
  c.sections.flatMap fun
    | .canons xs => xs.filterMap fun
      | .builtin b => some b
      | .canon _ => none
    | .sec _ => []

/-- The `canon` definitions of the verified grammar of a parsed component, in order. -/
def XComp.canons (c : XComp) : List Canon :=
  c.sections.flatMap fun
    | .canons xs => xs.filterMap fun
      | .canon d => some d
      | .builtin _ => none
    | .sec _ => []

/-! ## Grammar -/

/-- A boolean flag byte (`0x00`, `0x01`). -/
def flagG : Grammar Bool := tagged "flag" fun b => match b.toNat with
  | 0x00 => tag0 false
  | 0x01 => tag0 true
  | _ => none

/-- A type index and options. -/
def tOptsG (mk : Nat → List CanonOpt → Builtin) : Grammar XCanon :=
  (u32.seq canonOptsG).map fun p => .builtin (mk p.1 p.2)

/-- A type index and a flag. -/
def tFlagG (mk : Nat → Bool → Builtin) : Grammar XCanon :=
  (u32.seq flagG).map fun p => .builtin (mk p.1 p.2)

/-- A type index. -/
def tG (mk : Nat → Builtin) : Grammar XCanon := u32.map fun t => .builtin (mk t)

/-- A built-in without immediates. -/
def b0 (b : Builtin) : Option (Grammar XCanon) := tag0 (.builtin b)

/-- `canon` items by opcode: `Binary.md`'s `canon` productions that the verified grammar has,
and the built-ins `wasm-jco` emits. -/
def xcanonK (b : UInt8) : Option (Grammar XCanon) := match b.toNat with
  | 0x00 => some ((expect "canon lift" 0x00).then_
      (((u32.seq canonOptsG).seq u32).map fun p => .canon (.lift p.1.1 p.1.2 p.2)))
  | 0x01 => some ((expect "canon lower" 0x00).then_
      ((u32.seq canonOptsG).map fun p => .canon (.lower p.1 p.2)))
  | 0x02 => some (u32.map fun t => .canon (.resourceNew t))
  | 0x03 => some (u32.map fun t => .canon (.resourceDrop t))
  | 0x04 => some (u32.map fun t => .canon (.resourceRep t))
  | 0x05 => b0 .taskCancel
  | 0x06 => some (flagG.map fun a => .builtin (.subtaskCancel a))
  | 0x09 => some ((resultListG.seq canonOptsG).map fun p => .builtin (.taskReturn p.1 p.2))
  | 0x0a => some ((expect "i32" 0x7f).then_ (u32.map fun i => .builtin (.contextGet i)))
  | 0x0b => some ((expect "i32" 0x7f).then_ (u32.map fun i => .builtin (.contextSet i)))
  | 0x0c => some (flagG.map fun c => .builtin (.threadYield c))
  | 0x0d => b0 .subtaskDrop
  | 0x0e => some (tG .streamNew)
  | 0x0f => some (tOptsG .streamRead)
  | 0x10 => some (tOptsG .streamWrite)
  | 0x11 => some (tFlagG .streamCancelRead)
  | 0x12 => some (tFlagG .streamCancelWrite)
  | 0x13 => some (tG .streamDropReadable)
  | 0x14 => some (tG .streamDropWritable)
  | 0x15 => some (tG .futureNew)
  | 0x16 => some (tOptsG .futureRead)
  | 0x17 => some (tOptsG .futureWrite)
  | 0x18 => some (tFlagG .futureCancelRead)
  | 0x19 => some (tFlagG .futureCancelWrite)
  | 0x1a => some (tG .futureDropReadable)
  | 0x1b => some (tG .futureDropWritable)
  | 0x1c => some (canonOptsG.map fun o => .builtin (.errorContextNew o))
  | 0x1d => some (canonOptsG.map fun o => .builtin (.errorContextDebugMessage o))
  | 0x1e => b0 .errorContextDrop
  | 0x1f => b0 .waitableSetNew
  | 0x20 => some ((flagG.seq u32).map fun p => .builtin (.waitableSetWait p.1 p.2))
  | 0x21 => some ((flagG.seq u32).map fun p => .builtin (.waitableSetPoll p.1 p.2))
  | 0x22 => b0 .waitableSetDrop
  | 0x23 => b0 .waitableJoin
  | 0x24 => b0 .backpressureInc
  | 0x25 => b0 .backpressureDec
  | _ => none

/-- A `canon` item. -/
def xcanonG : Grammar XCanon := tagged "canon" xcanonK

/-- The section productions of the verified grammar (`sectionG`), as a function of the tag. -/
def sectionK (c : GrammarE Ast) (t : Grammar DefType) (ht : Silmaril.Parse.ByteParse.NonEmpty t.G) :
    UInt8 → Option (Grammar Section) := fun b => match b.toNat with
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

/-- Sections of an output component, nested components at most `k` deep: a `canon` section
holds `XCanon` items, every other section is one of the verified grammar. -/
def xsectionK (k : Nat) (b : UInt8) : Option (Grammar XSec) :=
  if b.toNat = 0x08 then vecSection xcanonG (tagged_nonEmpty _ _) XSec.canons
  else (sectionK (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _) b).map (Grammar.map .sec)

/-- A section of an output component. -/
def xsectionG (k : Nat) : Grammar XSec := tagged "section" (xsectionK k)

/-- An output component: the preamble, then sections to the end of the window. -/
def xcomponentG (k : Nat) : GrammarE XComp :=
  GrammarE.after (lit preambleBytes) fun _ =>
    (GrammarE.items (xsectionG k) (tagged_nonEmpty _ _)).map XComp.mk

/-- **Parse an output component of `wasm-jco`**, async built-ins included. -/
def xparse (bs : ByteArray) : Except Error XComp :=
  runAll (xcomponentG bs.size).parse bs

end Silmaril.Wasm.JcoTool
