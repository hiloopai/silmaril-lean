module

public import Silmaril.Wasm.Binaryen.MergeBack
public import Silmaril.Wasm.Behaviour.Semantics.Core

@[expose] public section

/-! # Linked behaviour sets without typing

`link_sound` (`Binaryen/Merge.lean`) compares the behaviour sets of a typed
invocation. `Program.beh` does not assume `InvokeOk`, so `merge_sound` needs the
comparison for every argument list. This file gives it for both store relations of
the linker, without configuration typing:

* `renamed_behaviours`: a global-address renaming (`GlobalPermutation.Renamed`)
  keeps behaviour sets. The renaming simulation is untyped and the relation is
  symmetric.
* `related_behaviours`: the linking relation (`StoreRelation.Related`) keeps
  behaviour sets when the source store's bodies are index-scoped (`StoreSc`).
  Forward, `WholeSimulation.step` only needs annotation scoping, which every step
  preserves (`xas_step`); backward, a linked step implies a source step
  (`MergeBack.back`), so a stuck source has a stuck linked configuration. With
  determinism of the profile this replaces `LinkBehaviours.stuck_transfer`, which
  needed typing.
-/

namespace Silmaril.Wasm.Binaryen.MergeUntyped

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Link.GC
open Silmaril.Wasm.Link.GC.AdminRelation

variable {H : Type}

/-! ## Global renaming -/

theorem renamed_sub {P : Profile} {p : Nat ≃ Nat} {s t : Store H}
    (ren : GlobalPermutation.Renamed p s t) (a : Nat) (vs : List Val) :
    behaviours P Simulation.noHost s a vs ⊆ behaviours P Simulation.noHost t a vs := by
  rintro b (⟨S, r, hS, hSr, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨T, hT, -, hTr⟩ := GlobalRenameSimulation.invoke_result ren hS hSr
    exact Or.inl ⟨_, r, hT, hTr, rfl⟩
  · refine Or.inr ⟨rfl, ?_⟩
    change InfiniteTrace (Step P Simulation.noHost) (invoke t a vs)
    rw [← GlobalRenameSimulation.config_invoke ren a vs]
    refine InfiniteTrace.coinduct
      (fun c => ∃ (S : Config H) (T : Store H), c = GlobalRenameSimulation.config p T S ∧
        GlobalPermutation.Renamed p S.store T ∧ InfiniteTrace (Step P Simulation.noHost) S)
      ?_ ⟨_, _, rfl, ren, hdiv⟩
    rintro c ⟨S, T, rfl, hren, hinf⟩
    obtain ⟨S₁, hS₁, hinf₁⟩ := hinf.unfold
    obtain ⟨T₁, hstep, hren₁⟩ := GlobalRenameSimulation.step hS₁ hren
    exact ⟨_, hstep, S₁, T₁, rfl, hren₁, hinf₁⟩

/-- **Global renaming keeps behaviour sets**, for every argument list. -/
theorem renamed_behaviours {P : Profile} {p : Nat ≃ Nat} {s t : Store H}
    (ren : GlobalPermutation.Renamed p s t) (a : Nat) (vs : List Val) :
    behaviours P Simulation.noHost t a vs = behaviours P Simulation.noHost s a vs :=
  Set.Subset.antisymm (renamed_sub ren.symm a vs) (renamed_sub ren a vs)

/-! ## The linking relation -/

theorem fwd_step {P : Profile} {mode : Mode} {S S' T : Config H}
    (h : Step P Simulation.noHost S S') (hm : Simulation.Matching mode S T)
    (hsc : XAs S.frame.module S.code) (hs : StoreSc S.store) :
    ∃ T', Step P Simulation.noHost T T' ∧ Simulation.Matching mode S' T' ∧
      XAs S'.frame.module S'.code ∧ StoreSc S'.store := by
  obtain ⟨T', hT, hm'⟩ := WholeSimulation.step h hm (xas_admins hsc) hs.functionScopes
  exact ⟨T', hT, hm', xas_step h hs hsc, hs.of_funcs (funcs_step h)⟩

theorem fwd_steps {P : Profile} {mode : Mode} {S S' T : Config H}
    (h : Steps P Simulation.noHost S S') (hm : Simulation.Matching mode S T)
    (hsc : XAs S.frame.module S.code) (hs : StoreSc S.store) :
    ∃ T', Steps P Simulation.noHost T T' ∧ Simulation.Matching mode S' T' ∧
      XAs S'.frame.module S'.code ∧ StoreSc S'.store := by
  induction h with
  | refl => exact ⟨T, .refl, hm, hsc, hs⟩
  | tail _ hstep ih =>
    obtain ⟨T₁, hT₁, hm₁, hsc₁, hs₁⟩ := ih
    obtain ⟨T₂, hT₂, hm₂, hsc₂, hs₂⟩ := fwd_step hstep hm₁ hsc₁ hs₁
    exact ⟨T₂, hT₁.tail hT₂, hm₂, hsc₂, hs₂⟩

theorem fwd_diverges {P : Profile} {mode : Mode} {S T : Config H}
    (hm : Simulation.Matching mode S T) (hsc : XAs S.frame.module S.code)
    (hs : StoreSc S.store) (hd : Diverges P Simulation.noHost S) :
    Diverges P Simulation.noHost T := by
  refine InfiniteTrace.coinduct
    (fun c => ∃ S, Simulation.Matching mode S c ∧ XAs S.frame.module S.code ∧
      StoreSc S.store ∧ InfiniteTrace (Step P Simulation.noHost) S) ?_ ⟨S, hm, hsc, hs, hd⟩
  rintro c ⟨S, hm, hsc, hs, hinf⟩
  obtain ⟨S₁, hS₁, hinf₁⟩ := hinf.unfold
  obtain ⟨T₁, hT₁, hm₁, hsc₁, hs₁⟩ := fwd_step hS₁ hm hsc hs
  exact ⟨T₁, hT₁, S₁, hm₁, hsc₁, hs₁, hinf₁⟩

/-- A stuck scoped source configuration has a stuck linked counterpart. -/
theorem stuck_back {P : Profile} {mode : Mode} {S T : Config H}
    (hm : Simulation.Matching mode S T) (hsc : XAs S.frame.module S.code)
    (hno : ∀ z, ¬ Step P Simulation.noHost S z) : ∀ z, ¬ Step P Simulation.noHost T z := by
  intro z hz
  obtain ⟨c, hc⟩ := back hz hm.stores hm.frames hm.code hsc
  exact hno c hc

/-- A terminal linked configuration has the same terminal source. -/
theorem terminal_back {mode : Mode} {S T : Config H} {r : Result}
    (hm : Simulation.Matching mode S T) (hT : T.code = r.toAdmin) : S.code = r.toAdmin := by
  have hc := hm.code
  rw [hT] at hc
  cases r with
  | values vs => exact hc.vals_right_exact
  | trap =>
    simp only [Result.toAdmin] at hc ⊢
    obtain ⟨R, h1, h2⟩ := hc.trap_right
    rw [h1, h2.nil_right]
  | throw a =>
    simp only [Result.toAdmin] at hc ⊢
    obtain ⟨R, h1, h2⟩ := hc.ref_right
    obtain ⟨R', h3, h4⟩ := h2.throwRef_right
    rw [h1, h3, h4.nil_right]

theorem invoke_matching {s t : Store H} (rel : StoreRelation.Related s t) (a : Nat)
    (vs : List Val) : Simulation.Matching .same (invoke s a vs) (invoke t a vs) := by
  refine ⟨rel, Frames.same {}, ?_⟩
  simp only [Execution.Core.invoke, rel.function_tag_lookup a]
  exact Control.same _ _

theorem invoke_scope (s : Store H) (a : Nat) (vs : List Val) :
    XAs (invoke s a vs).frame.module (invoke s a vs).code := by
  simp [Execution.Core.invoke]

/-- **The linking relation keeps behaviour sets**, for every argument list, when
the source store's bodies are scoped. -/
theorem related_behaviours {o : SingleThreaded.GrowOracle} {s t : Store H}
    (rel : StoreRelation.Related s t) (hs : StoreSc s) (a : Nat) (vs : List Val) :
    behaviours (SingleThreaded.profile o) Simulation.noHost t a vs =
      behaviours (SingleThreaded.profile o) Simulation.noHost s a vs := by
  have m0 := invoke_matching rel a vs
  have sc0 := invoke_scope s a vs
  ext b
  constructor
  · rintro (⟨T, r, hT, hTr, rfl⟩ | ⟨rfl, hdiv⟩)
    · rcases LinkBehaviours.diverges_or_nf (invoke s a vs) with hsd | ⟨S, hS, hSnf⟩
      · exact absurd (fwd_diverges m0 sc0 hs hsd)
          (LinkBehaviours.no_diverges_of_nf hT (LinkObservation.result_terminal hTr))
      · obtain ⟨T', hT', hm', hsc', -⟩ := fwd_steps hS m0 sc0 hs
        have hTnf := stuck_back hm' hsc' hSnf
        have heq : T' = T := SingleThreaded.nf_unique_of_join
          (fun ha hb => SingleThreaded.Det.DStep.join' ha hb) hT' hT hTnf
          (LinkObservation.result_terminal hTr)
        subst heq
        exact Or.inl ⟨S, r, hS, terminal_back hm' hTr, rfl⟩
    · rcases LinkBehaviours.diverges_or_nf (invoke s a vs) with hsd | ⟨S, hS, hSnf⟩
      · exact Or.inr ⟨rfl, hsd⟩
      · exfalso
        obtain ⟨T', hT', hm', hsc', -⟩ := fwd_steps hS m0 sc0 hs
        exact LinkBehaviours.no_diverges_of_nf hT' (stuck_back hm' hsc' hSnf) hdiv
  · rintro (⟨S, r, hS, hSr, rfl⟩ | ⟨rfl, hdiv⟩)
    · obtain ⟨T, hT, hm', -, -⟩ := fwd_steps hS m0 sc0 hs
      exact Or.inl ⟨T, r, hT, LinkObservation.paired_result hm' hSr, rfl⟩
    · exact Or.inr ⟨rfl, fwd_diverges m0 sc0 hs hdiv⟩

end Silmaril.Wasm.Binaryen.MergeUntyped
