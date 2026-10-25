module

public import Silmaril.Wasm.Binaryen.MergeBackContext
public import Silmaril.Wasm.Binaryen.MergeUntyped

@[expose] public section

/-! # Run and divergence transport from exact backward merge steps

These reusable helpers consume a chosen-target backward-step law. Every actual
source step preserves annotation scope and the scope of stored function bodies;
finite and infinite target executions therefore transport at the same numerical
profile. No configuration typing or numerical determinism is used.
-/

namespace Silmaril.Wasm.Binaryen.MergeUntyped

open Execution.Core Numerics
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.AdminRelation

variable {H : Type} {P : Profile}

/-- Exact matching of every target step, for any related scoped source. -/
abbrev BackMatching (P : Profile) (H : Type) : Prop :=
  ∀ {target target' : Config H}, Step P Simulation.noHost target target' →
    BackwardStep P Simulation.noHost target target'

theorem bwd_step_of (hback : BackMatching P H) {mode : Mode} {S T T' : Config H}
    (h : Step P Simulation.noHost T T') (hm : Simulation.Matching mode S T)
    (hsc : XAs S.frame.module S.code) (hs : StoreSc S.store) :
    ∃ S', Step P Simulation.noHost S S' ∧ Simulation.Matching mode S' T' ∧
      XAs S'.frame.module S'.code ∧ StoreSc S'.store := by
  obtain ⟨S', actual, matching⟩ := hback h hm hsc
  exact ⟨S', actual, matching, xas_step actual hs hsc,
    hs.of_funcs (funcs_step actual)⟩

theorem bwd_steps_of (hback : BackMatching P H) {mode : Mode} {S T T' : Config H}
    (h : Steps P Simulation.noHost T T') (hm : Simulation.Matching mode S T)
    (hsc : XAs S.frame.module S.code) (hs : StoreSc S.store) :
    ∃ S', Steps P Simulation.noHost S S' ∧ Simulation.Matching mode S' T' ∧
      XAs S'.frame.module S'.code ∧ StoreSc S'.store := by
  induction h with
  | refl => exact ⟨S, .refl, hm, hsc, hs⟩
  | tail _ hstep ih =>
    obtain ⟨S₁, hS₁, hm₁, hsc₁, hs₁⟩ := ih
    obtain ⟨S₂, hS₂, hm₂, hsc₂, hs₂⟩ := bwd_step_of hback hstep hm₁ hsc₁ hs₁
    exact ⟨S₂, hS₁.tail hS₂, hm₂, hsc₂, hs₂⟩

theorem bwd_diverges_of (hback : BackMatching P H) {mode : Mode} {S T : Config H}
    (hm : Simulation.Matching mode S T) (hsc : XAs S.frame.module S.code)
    (hs : StoreSc S.store) (hd : Diverges P Simulation.noHost T) :
    Diverges P Simulation.noHost S := by
  refine InfiniteTrace.coinduct
    (fun c => ∃ T, Simulation.Matching mode c T ∧ XAs c.frame.module c.code ∧
      StoreSc c.store ∧ InfiniteTrace (Step P Simulation.noHost) T)
    ?_ ⟨T, hm, hsc, hs, hd⟩
  rintro c ⟨T, hm, hsc, hs, hinf⟩
  obtain ⟨T₁, hT₁, hinf₁⟩ := hinf.unfold
  obtain ⟨S₁, hS₁, hm₁, hsc₁, hs₁⟩ := bwd_step_of hback hT₁ hm hsc hs
  exact ⟨S₁, hS₁, T₁, hm₁, hsc₁, hs₁, hinf₁⟩

/-- Both directions retain each actual terminating result and every infinite
trace, including all nondeterministic numerical choices. -/
theorem matching_behavioursOf_of_back_matching (hback : BackMatching P H)
    {mode : Mode} {S T : Config H} (hm : Simulation.Matching mode S T)
    (hsc : XAs S.frame.module S.code) (hs : StoreSc S.store) :
    behavioursOf P Simulation.noHost T = behavioursOf P Simulation.noHost S := by
  ext b
  constructor
  · rintro (⟨T', r, hT, hTr, rfl⟩ | ⟨rfl, hdiv⟩)
    · obtain ⟨S', hS, hm', -, -⟩ := bwd_steps_of hback hT hm hsc hs
      exact Or.inl ⟨S', r, hS, terminal_back hm' hTr, rfl⟩
    · exact Or.inr ⟨rfl, bwd_diverges_of hback hm hsc hs hdiv⟩
  · rintro (⟨S', r, hS, hSr, rfl⟩ | ⟨rfl, hdiv⟩)
    · obtain ⟨T', hT, hm', -, -⟩ := fwd_steps hS hm hsc hs
      exact Or.inl ⟨T', r, hT, LinkObservation.paired_result hm' hSr, rfl⟩
    · exact Or.inr ⟨rfl, fwd_diverges hm hsc hs hdiv⟩

/-- Invocation arguments are unrestricted; the sole store invariant is scope
of stored function bodies. -/
theorem related_behaviours_of_back_matching (hback : BackMatching P H) {s t : Store H}
    (rel : StoreRelation.Related s t) (hs : StoreSc s) (a : Nat) (vs : List Val) :
    behaviours P Simulation.noHost t a vs = behaviours P Simulation.noHost s a vs :=
  matching_behavioursOf_of_back_matching hback (invoke_matching rel a vs)
    (invoke_scope s a vs) hs

end Silmaril.Wasm.Binaryen.MergeUntyped
