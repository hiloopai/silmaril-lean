module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.WeakeningSplit

/-! # Variables as structural weakening

Selecting a variable agrees with weakening to its linear singleton and then
removing the packed empty-context unit. This exposes variable interpretation
through the same context-map interface as all other constructors.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation

universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

/-- Equal index embeddings have the same structural interpretation. -/
theorem weakenPure_congr (N : SeqData.{u,v,w,r} τ Φ ε) {n m : Nat}
    {Γ : QCtx τ n} {Δ : QCtx τ m} {ρ σ : Fin m → Fin n}
    (h : QCtx.Weakening Γ Δ ρ) (k : QCtx.Weakening Γ Δ σ) (he : ρ = σ) :
    weakenPure N h = weakenPure N k := by
  subst σ
  rfl

theorem variablePure_eq_weaken {n : Nat} {Γ : QCtx τ n} (i : Fin n) (h : Γ.VarAllowed i) :
    variablePure M.toSeqData i h =
      pureCompose M.toSeqData
        (weakenPure M.toSeqData ((QCtx.varAllowed_iff_weakening_singleton i).mp h))
        ⟨M.leftUnitor (Γ i).1, M.toSeqData.leftUnitor_pure _⟩ := by
  induction Γ using QCtx.inductionOn with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A q ih =>
    cases i using Fin.cases with
    | zero =>
      have ht : Γ.Discardable := fun j => h.2 j.succ (Fin.succ_ne_zero _)
      let hw := (QCtx.discardable_iff_weakening_nil).mp ht
      have hq : Usage.effective (.used .linear) (quantity A) ≤ Usage.effective q (quantity A) := h.1
      have he : (fun _ : Fin 1 => (0 : Fin (n+1))) =
          Fin.cases 0 (fun j : Fin 0 => (Fin.elim0 j : Fin n).succ) := by
        funext j
        exact Fin.cases rfl (fun k => Fin.elim0 k) j
      have hew := weakenPure_congr M.toSeqData
        ((QCtx.varAllowed_iff_weakening_singleton (0 : Fin (n+1))).mp h)
        (QCtx.Weakening.cons hw hq) he
      rw [hew]
      change variablePure M.toSeqData 0 h = pureCompose M.toSeqData
        (weakenPure M.toSeqData (QCtx.Weakening.cons hw hq))
        ⟨M.leftUnitor A, M.toSeqData.leftUnitor_pure A⟩
      rw [weakenPure_cons M hw hq]
      cases q with
      | zero => exact False.elim hq
      | used q =>
        change pureCompose M.toSeqData
          (pureRight M.toSeqData ⟨discard M.toSeqData ht, discard_pure _ ht⟩ A)
          ⟨M.leftUnitor A, M.toSeqData.leftUnitor_pure A⟩ =
            pureCompose M.toSeqData (pureRight M.toSeqData (weakenPure M.toSeqData hw) A)
              ⟨M.leftUnitor A, M.toSeqData.leftUnitor_pure A⟩
        have hd : weakenPure M.toSeqData hw =
            ⟨discard M.toSeqData ht, discard_pure _ ht⟩ := Subtype.ext (weaken_nil M hw)
        rw [hd]
        rfl
    | succ i =>
      have ht : Γ.VarAllowed i :=
        ⟨h.1, fun j hj => h.2 j.succ (fun he => hj (Fin.succ_injective _ he))⟩
      have hz : Usage.zero ≤ Usage.effective q (quantity A) := h.2 0 (Ne.symm (Fin.succ_ne_zero i))
      let hw := (QCtx.varAllowed_iff_weakening_singleton i).mp ht
      have hew : weakenPure M.toSeqData ((QCtx.varAllowed_iff_weakening_singleton i.succ).mp h) =
          weakenPure M.toSeqData (QCtx.Weakening.skip hw hz) := rfl
      rw [hew, weakenPure_skip M hw hz]
      cases q with
      | zero => exact ih i ht
      | used q =>
        have ha : Quantity.affine ≤ quantity A :=
          ((Usage.zero_le_effective_iff _ _).mp hz).trans inf_le_left
        change dropRight M.toSeqData (variablePure M.toSeqData i ht) A ha =
          pureCompose M.toSeqData (dropRight M.toSeqData (weakenPure M.toSeqData hw) A ha)
            ⟨M.leftUnitor (Γ i).1, M.toSeqData.leftUnitor_pure _⟩
        rw [ih i ht, dropRight_compose]

/-- The underlying variable arrow factors through its linear singleton. -/
theorem variable_eq_weaken {n : Nat} {Γ : QCtx τ n} (i : Fin n) (h : Γ.VarAllowed i) :
    «variable» M.toSeqData i h = M.compose
      (weaken M.toSeqData ((QCtx.varAllowed_iff_weakening_singleton i).mp h))
      (M.leftUnitor (Γ i).1) :=
  congrArg Subtype.val (variablePure_eq_weaken M i h)

end Silmaril.Isotope.Refinement.Models.Denotation
