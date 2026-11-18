module

public import Silmaril.Machine.Vex.CFG.CallEdges.Defs

public section

namespace Silmaril.Machine.Vex.ControlFlow.Proofs

variable {Label Function : Type*} {part : Partition Label Function} {focus : Function} {graph : CallCFG Label}

theorem embed_flow (noCalls : graph.NoCalls) : CallCFG.embed graph.flow = graph := by
  cases graph with
  | mk flow calls =>
    exact congrArg (CallCFG.mk flow) (funext fun origin => (noCalls origin).symm)

theorem flat_image (wf : CallCFG.WellFormed part focus graph) :
    graph.InFlatImage part focus ↔ graph.NoCalls := by
  constructor
  · rintro ⟨_, _, rfl⟩ origin
    rfl
  · intro noCalls
    exact ⟨graph.flow, wf.flow, embed_flow noCalls⟩

theorem no_calls_of_no_internal_or_external (wf : CallCFG.WellFormed part focus graph)
    (noInternal : ¬ graph.HasInternalCall part) (noExternal : ¬ graph.HasExternalCall part) :
    graph.NoCalls := by
  intro origin
  cases found : graph.calls origin with
  | none => rfl
  | some site =>
    have edge : Edge.call site.callee ∈ graph.edges origin := ⟨site, found, rfl⟩
    rcases (wf.callSite origin site found).2.2.1 with internal | external
    · obtain ⟨callee, owned, _⟩ := internal
      exact False.elim (noInternal ⟨origin, site.callee, edge, callee, owned⟩)
    · exact False.elim (noExternal ⟨origin, site.callee, edge, external⟩)

theorem in_flat_image_iff_no_internal (wf : CallCFG.WellFormed part focus graph)
    (noExternal : ¬ graph.HasExternalCall part) : graph.InFlatImage part focus ↔ ¬ graph.HasInternalCall part := by
  rw [flat_image wf]
  refine ⟨?_, fun noInternal => no_calls_of_no_internal_or_external wf noInternal noExternal⟩
  rintro noCalls ⟨origin, callee, ⟨site, found, _⟩, _⟩
  rw [noCalls origin] at found
  cases found

theorem common_row {FlatRow : Silmaril.Semantics.Region.Tree.FlatCFG Label → Prop} {CallRow : CallCFG Label → Prop}
    (agrees : ∀ flat, CallRow (CallCFG.embed flat) ↔ FlatRow flat)
    (wf : CallCFG.WellFormed part focus graph) (noExternal : ¬ graph.HasExternalCall part) :
    (∃ flat, FlatWellFormed part focus flat ∧ CallCFG.embed flat = graph ∧ FlatRow flat) ↔
      ¬ graph.HasInternalCall part ∧ CallRow graph := by
  have overlap := in_flat_image_iff_no_internal wf noExternal
  constructor
  · rintro ⟨flat, flatWF, equal, row⟩
    exact ⟨overlap.mp ⟨flat, flatWF, equal⟩, equal ▸ (agrees flat).mpr row⟩
  · rintro ⟨noInternal, row⟩
    obtain ⟨flat, flatWF, rfl⟩ := overlap.mpr noInternal
    exact ⟨flat, flatWF, rfl, (agrees flat).mp row⟩

end Silmaril.Machine.Vex.ControlFlow.Proofs
