module

public import Silmaril.Compiler.Native.Optimize.Validation.Thms
/-! Exact observations of the existing executable validator. These names expose
its actual runs and their order; no concrete candidate execution is assumed. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Acceptance

open Silmaril.Compile

def observedRegs (source : Mir.Block) : List Nat :=
  (source.instrs.toList.flatMap defs).dedup

def sourceRun (source : Mir.Block) : (Term × List Nat) × State :=
  (evalBlock source (observedRegs source)).run {}

def candidateRun (source candidate : Mir.Block) : (Term × List Nat) × State :=
  (evalBlock candidate (observedRegs source)).run { nodes := (sourceRun source).2.nodes }

def slotNames (source candidate : Mir.Block) : List Nat :=
  ((sourceRun source).2.slots.map (·.1) ++
    (candidateRun source candidate).2.slots.map (·.1)).dedup

def sourceSlotRun (source candidate : Mir.Block) : List Nat × State :=
  ((slotNames source candidate).mapM readSlot).run
    { (sourceRun source).2 with nodes := (candidateRun source candidate).2.nodes }

def candidateSlotRun (source candidate : Mir.Block) : List Nat × State :=
  ((slotNames source candidate).mapM readSlot).run
    { (candidateRun source candidate).2 with nodes := (sourceSlotRun source candidate).2.nodes }

/-- Facts extracted from actual acceptance, before any concrete semantic proof.
The suffix guard precedes both slot-read runs; outputs precede those reads too. -/
structure Accepted (freshBase : Nat) (source candidate : Mir.Block) : Prop where
  source_size : source.instrs.size ≤ 4096
  candidate_size : candidate.instrs.size ≤ 8192
  writes : (candidate.instrs.all fun i => (defs i).all fun r =>
    freshBase ≤ r || (observedRegs source).contains r) = true
  partialLeaves : (candidateRun source candidate).2.nodes.any Expr.isPartialLeaf
    (sourceRun source).2.nodes.size = false
  term : (sourceRun source).1.1 = (candidateRun source candidate).1.1
  observed : (sourceRun source).1.2 = (candidateRun source candidate).1.2
  effects : (sourceRun source).2.effects = (candidateRun source candidate).2.effects
  slots : (sourceSlotRun source candidate).1 = (candidateSlotRun source candidate).1

end Silmaril.Compiler.Native.Optimize.Validation.Acceptance
