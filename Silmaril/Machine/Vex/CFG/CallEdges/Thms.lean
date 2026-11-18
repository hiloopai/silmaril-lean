module

public import Silmaril.Machine.Vex.CFG.CallEdges.Defs
import Silmaril.Proofs.Machine.Vex.CFG.CallEdges

public section

namespace Silmaril.Machine.Vex.ControlFlow

open Silmaril.Semantics.Region.Tree (FlatCFG)

variable {Label Function : Type*} {part : Partition Label Function} {focus : Function} {graph : CallCFG Label}

@[simp] theorem CallCFG.flow_embed (flat : FlatCFG Label) : (embed flat).flow = flat := rfl

theorem CallCFG.embed_flow (noCalls : graph.NoCalls) : embed graph.flow = graph := Proofs.embed_flow noCalls

@[simp] theorem CallCFG.edges_embed (flat : FlatCFG Label) : (embed flat).edges = ordinaryEdges flat := by
  funext origin
  ext edge; cases edge <;> simp [embed, edges, ordinaryEdges]

@[simp] theorem CallCFG.wellFormed_embed {flat : FlatCFG Label} :
    WellFormed part focus (embed flat) ↔ FlatWellFormed part focus flat := by
  refine ⟨WellFormed.flow, fun wf => ⟨wf, ?_⟩⟩
  intro origin site found; cases found

theorem CallCFG.inFlatImage_iff_noCalls (wf : WellFormed part focus graph) :
    graph.InFlatImage part focus ↔ graph.NoCalls := Proofs.flat_image wf

/-- In this profile opaque external-call summaries have not been identified
with ordinary exits. Restrict them out when characterizing the overlap. -/
theorem CallCFG.inFlatImage_iff_noInternalCall (wf : WellFormed part focus graph)
    (noExternal : ¬ graph.HasExternalCall part) : graph.InFlatImage part focus ↔ ¬ graph.HasInternalCall part :=
  Proofs.in_flat_image_iff_no_internal wf noExternal

/-- Lift exact graph overlap to any pair of row predicates that agrees on the embedding. -/
theorem CallCFG.commonRow_iff {FlatRow : FlatCFG Label → Prop} {CallRow : CallCFG Label → Prop}
    (agrees : ∀ flat, CallRow (embed flat) ↔ FlatRow flat)
    (wf : WellFormed part focus graph) (noExternal : ¬ graph.HasExternalCall part) :
    (∃ flat, FlatWellFormed part focus flat ∧ embed flat = graph ∧ FlatRow flat) ↔
      ¬ graph.HasInternalCall part ∧ CallRow graph := Proofs.common_row agrees wf noExternal

end Silmaril.Machine.Vex.ControlFlow
