module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Case.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Typing.Expected.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms

/-! # Schedule written operands before native LambdaSSA packing -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Native

open LambdaSSA (FiniteCFG Flat Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive region)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (PacketType PrimitiveSignature)

universe u w
variable {F : Type} {labels blocks exits captures : Nat}
  {sig : PrimitiveSignature F} {context : BoundCtx PacketType captures}
  {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
  {source : FiniteCFG F blocks exits captures}

/-- Reconstruct the scheduled syntax with its original finite scopes.
Ascriptions are indexed by syntax positions, so scoping keeps them in place. -/
def scheduleFlatWithBindings [DecidableEq F] (sig : PrimitiveSignature F)
    (types : Fin labels → PacketType) (context : BoundCtx PacketType captures)
    (written : Flat F labels captures) :
    Option ({row : Flat F labels captures // scheduleCases sig types context.toList written.erase = some row.erase}
      × NamedFlat.BindingTypes PacketType) :=
  match accepted : scheduleWithBindings sig types context.toList written.erase with
  | none => none
  | some (prepared, bindings) => (scopedRow labels captures prepared).map fun row =>
    have scheduled : scheduleCases sig types context.toList written.erase = some prepared :=
      congrArg (Option.map Prod.fst) accepted
    (⟨row.val, scheduled.trans (congrArg some row.property.symm)⟩, bindings)

def scheduleFlat [DecidableEq F] (sig : PrimitiveSignature F)
    (types : Fin labels → PacketType) (context : BoundCtx PacketType captures)
    (written : Flat F labels captures) :
    Option {row : Flat F labels captures // scheduleCases sig types context.toList written.erase = some row.erase} :=
  (scheduleFlatWithBindings sig types context written).map Prod.fst

structure Compiled (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  code : FiniteCFG F blocks exits captures
  entry_eq : ∃ check : DecidableEq F,
    @scheduleCases F check sig (blocks + exits) (SSA.FiniteSum.append packets outputs) context.toList
      source.entry.erase = some code.entry.erase
  row_eq : ∀ i, ∃ check : DecidableEq F,
    @scheduleCases F check sig (blocks + exits) (SSA.FiniteSum.append packets outputs)
      (BoundCtx.snoc context (packets i)).toList (source.block i).erase = some (code.block i).erase
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  codeTyped : letI := sig.typing; code.HasType context packets outputs

/-- Schedule each written row in its original context. Native packing
accepts sum residuals directly and needs no fresh row or label relocation. -/
def compile [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Compiled sig context packets outputs source) :=
  letI := sig.typing
  if original : NamedFlat.checkExpected source context packets outputs = true then do
    let types := SSA.FiniteSum.append packets outputs
    let (entry, entryBindings) ← scheduleFlatWithBindings sig types context source.entry
    let rows ← tabulateDependent blocks fun i =>
      scheduleFlatWithBindings sig types (.snoc context (packets i)) (source.block i)
    let code : FiniteCFG F blocks exits captures := ⟨entry.val, fun i => (rows i).1.val⟩
    let rowBindings := fun i => (rows i).2
    if typed : NamedFlat.checkWithBindings code context packets outputs entryBindings rowBindings = true then
      return ⟨code, ⟨inferInstance, entry.property⟩, fun i => ⟨inferInstance, (rows i).1.property⟩,
        NamedFlat.checkExpected_sound _ _ _ _ original, NamedFlat.checkWithBindings_sound _ _ _ _ _ _ typed⟩
    else none
  else none

def Compiled.packedRegion (built : Compiled sig context packets outputs source) : Region F :=
  letI := sig.typing
  (FiniteCFG.packedExecutionRegion built.codeTyped).packInputsDestructure context.toList

/-- Execute the actual packed LambdaSSA program with its pure capture record. -/
noncomputable def Compiled.observe {Events : Type w → Type w} {A : Type u}
    (built : Compiled sig context packets outputs source) (instr : Primitive Events F A)
    (ambient : Env A) (record : Value A) :=
  region instr (extend ambient record) built.packedRegion

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Native
