module

public import Silmaril.Logic.HOLLight.Kernel

@[expose] public section

namespace Silmaril.Logic.HOLLight

namespace HasType

theorem equal_inv {sig : Signature} {Γ : List Ty} {A : Ty} {s t : Tm}
    (h : HasType sig Γ (Tm.equal A s t) .bool) :
    HasType sig Γ s A ∧ HasType sig Γ t A := by
  cases h with
  | app hf ht =>
    cases hf with
    | app hc hs =>
      cases hc with
      | const hc => cases hc; exact ⟨hs, ht⟩

theorem of_rename {sig : Signature} {Γ Δ : List Ty} {A : Ty} {t : Tm}
    {ρ : Nat → Nat} (h : HasType sig Δ (t.rename ρ) A)
    (compatible : ∀ i B, Δ[ρ i]? = some B → Γ[i]? = some B) : HasType sig Γ t A := by
  induction t generalizing Γ Δ ρ A with
  | bvar i => cases h with | bvar hi wf => exact .bvar (compatible i _ hi) wf
  | fvar n A => cases h with | fvar _ wf => exact .fvar n wf
  | const c => cases h with | const hc => exact .const hc
  | app f x ihf ihx =>
    cases h with
    | app hf hx => exact .app (ihf hf compatible) (ihx hx compatible)
  | lam B b ih =>
    cases h with
    | lam wf hb =>
      apply HasType.lam wf
      apply ih hb
      intro i C hi
      cases i with
      | zero => exact hi
      | succ i => exact compatible i C hi

theorem closed_context {sig : Signature} {Γ : List Ty} {t : Tm} {A : Ty}
    (h : HasType sig [] t A) : HasType sig Γ t A := by
  have h' := h.rename (Δ := Γ) id (by intro i B hi; simp at hi)
  simpa using h'

theorem abstractFree {sig : Signature} {t : Tm} {A B : Ty}
    (ht : HasType sig [] t B) (hA : A.WellFormed sig.tyOps) (name : Nat) :
    HasType sig [A] (t.replaceFree (name, A) (.bvar 0)) B := by
  apply ht.closed_context.freeSubst
  intro n C hC
  split
  · rename_i heq
    have hCA : C = A := congrArg Prod.snd heq
    cases hCA
    exact .bvar rfl hA
  · exact .fvar n hC

end HasType

namespace Derives

theorem typing {sig : Signature} {theory : Theory} {H : Hyps} {p : Tm}
    (proof : Derives sig theory H p) : HasType sig [] p .bool := by
  induction proof with
  | «axiom» _ ht => exact ht.closed_context
  | refl ht => exact .equal ht.wf ht ht
  | trans _ _ ih₁ ih₂ =>
    exact .equal ih₁.equal_inv.1.wf ih₁.equal_inv.1 ih₂.equal_inv.2
  | mkComb _ _ ih₁ ih₂ =>
    exact .equal ih₁.equal_inv.1.wf.2 (.app ih₁.equal_inv.1 ih₂.equal_inv.1)
      (.app ih₁.equal_inv.2 ih₂.equal_inv.2)
  | abs name wf _ _ ih =>
    exact .equal ⟨wf, ih.equal_inv.1.wf⟩
      (.lam wf (ih.equal_inv.1.abstractFree wf name))
      (.lam wf (ih.equal_inv.2.abstractFree wf name))
  | beta name wf ht _ =>
    exact .equal ht.wf (.app (.lam wf ht) (.fvar name wf)) (ht.open (.fvar name wf))
  | assume ht => exact ht
  | eqMp _ _ ih _ => exact ih.equal_inv.2
  | deductAntisym _ _ ih₁ ih₂ => exact .equal (by trivial) ih₁ ih₂
  | inst σ hσ _ ih => exact ih.freeSubst σ hσ
  | instType σ hσ _ ih => simpa using ih.tySubst σ hσ

theorem typedHyps {sig : Signature} {theory : Theory} {H : Hyps} {p : Tm}
    (proof : Derives sig theory H p) : TypedHyps sig [] H := by
  induction proof with
  | «axiom» | refl | beta => intro p hp; simp at hp
  | trans _ _ ih₁ ih₂ | mkComb _ _ ih₁ ih₂ | eqMp _ _ ih₁ ih₂ =>
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ih₁ p hp
    · exact ih₂ p hp
  | abs _ _ _ _ ih => exact ih
  | assume ht => intro p hp; have heq := Finset.mem_singleton.mp hp; subst p; exact ht
  | deductAntisym _ _ ih₁ ih₂ =>
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ih₁ p (Finset.mem_of_mem_erase hp)
    · exact ih₂ p (Finset.mem_of_mem_erase hp)
  | inst σ hσ _ ih =>
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (ih q hq).freeSubst σ hσ
  | instType σ hσ _ ih =>
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    simpa using (ih q hq).tySubst σ hσ

/-- Adjoin a typed assumption using deduction antisymmetry and equality modus ponens. -/
theorem addAssum {sig : Signature} {theory : Theory} {H : Hyps} {p q : Tm}
    (proof : Derives sig theory H p) (hq : HasType sig [] q .bool) :
    Derives sig theory (H ∪ {q}) p := by
  have hp := (Derives.assume hq).deductAntisym proof |>.eqMp (Derives.assume hq)
  have heq : (({q} : Hyps).erase p ∪ H.erase q) ∪ {q} = H ∪ {q} := by
    ext t
    by_cases ht : t = q <;> simp [ht]
  exact heq ▸ hp

theorem unionHyps {sig : Signature} {theory : Theory} {H K : Hyps} {p : Tm}
    (proof : Derives sig theory H p) (hK : TypedHyps sig [] K) :
    Derives sig theory (H ∪ K) p := by
  induction K using Finset.induction_on with
  | empty => simpa using proof
  | @insert q K hq ih =>
    have hK' : TypedHyps sig [] K := fun t ht => hK t (Finset.mem_insert_of_mem ht)
    have hq' := hK q (Finset.mem_insert_self q K)
    simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
      (ih hK').addAssum hq'

/-- Hypothesis weakening is admissible; it is not an extra inference constructor. -/
theorem weaken {sig : Signature} {theory : Theory} {H K : Hyps} {p : Tm}
    (proof : Derives sig theory H p) (hHK : H ⊆ K) (hK : TypedHyps sig [] K) :
    Derives sig theory K p := by
  simpa only [Finset.union_eq_right.mpr hHK] using proof.unionHyps hK

/-- Symmetry is derived from congruence and equality modus ponens. -/
theorem symm {sig : Signature} {theory : Theory} {H : Hyps}
    {A : Ty} {s t : Tm} (proof : Derives sig theory H (Tm.equal A s t)) :
    Derives sig theory H (Tm.equal A t s) := by
  have hs := proof.typing.equal_inv.1
  have heq : HasType sig [] (.const (.eq A)) (.arr A (.arr A .bool)) := .const (.eq hs.wf)
  have h := (Derives.refl heq).mkComb proof |>.mkComb (Derives.refl hs)
  have h' := h.eqMp (Derives.refl hs)
  simpa [Tm.equal] using h'

/-- Instantiate exactly one typed free variable in a theorem. -/
theorem replaceFree {sig : Signature} {theory : Theory} {H : Hyps} {p value : Tm}
    {A : Ty} (proof : Derives sig theory H p) (name : Nat)
    (hv : HasType sig [] value A) :
    Derives sig theory (H.image (fun t => t.replaceFree (name, A) value))
      (p.replaceFree (name, A) value) := by
  apply Derives.inst _ _ proof
  intro n B hB
  split
  · rename_i heq
    have hBA : B = A := congrArg Prod.snd heq
    cases hBA
    exact hv
  · exact .fvar n hB

/-- Beta conversion for any well-typed argument, derived from the fresh-variable rule. -/
theorem generalBeta {sig : Signature} {theory : Theory} {A B : Ty} {body value : Tm}
    (hb : HasType sig [A] body B) (hv : HasType sig [] value A) :
    Derives sig theory ∅ (Tm.equal B (.app (.lam A body) value) (body.open value)) := by
  let n := Tm.freshName [body]
  have hn : body.Fresh (n, A) := Tm.freshName_fresh [body] (by simp) A
  have hb' := Derives.beta (theory := theory) n hv.wf hb hn
  have h := hb'.replaceFree n hv
  have hlam : (Tm.lam A body).Fresh (n, A) := hn
  have hleft : (Tm.app (.lam A body) (.fvar n A)).replaceFree (n, A) value =
      .app (.lam A body) value := by
    change Tm.app ((Tm.lam A body).replaceFree (n, A) value)
      ((Tm.fvar n A).replaceFree (n, A) value) = _
    rw [Tm.replaceFree_of_fresh hlam, Tm.replaceFree_self]
  have hright := Tm.replaceFree_open_fvar hn hv.scope
  change Derives sig theory (Finset.image _ ∅)
    (Tm.equal B ((Tm.app (.lam A body) (.fvar n A)).replaceFree (n, A) value)
      ((body.open (.fvar n A)).replaceFree (n, A) value)) at h
  rw [Finset.image_empty, hleft, hright] at h
  exact h

/-- The opened-body presentation of abstraction, derived from named abstraction. -/
theorem absOpen {sig : Signature} {theory : Theory} {H : Hyps} {A B : Ty}
    {s t : Tm} (name : Nat) (hA : A.WellFormed sig.tyOps)
    (hs : HasType sig [A] s B) (ht : HasType sig [A] t B)
    (hsfresh : s.Fresh (name, A)) (htfresh : t.Fresh (name, A))
    (hH : ∀ p ∈ H, p.Fresh (name, A))
    (proof : Derives sig theory H
      (Tm.equal B (s.open (.fvar name A)) (t.open (.fvar name A)))) :
    Derives sig theory H (Tm.equal (.arr A B) (.lam A s) (.lam A t)) := by
  have h := proof.abs name hA hH
  simpa only [Tm.replaceFree_open_close hsfresh hs.scope,
    Tm.replaceFree_open_close htfresh ht.scope] using h

/-- Replace one assumed formula by its derivation. This is admissible cut. -/
theorem cut {sig : Signature} {theory : Theory} {H K : Hyps} {p q : Tm}
    (proof : Derives sig theory H p) (premise : Derives sig theory K q) :
    Derives sig theory (H.erase q ∪ K) p := by
  have result := (premise.deductAntisym proof).eqMp premise
  have context : (K.erase p ∪ H.erase q) ∪ K = H.erase q ∪ K := by
    ext t
    simp only [Finset.mem_union, Finset.mem_erase]
    tauto
  exact context ▸ result

private theorem cutAll {sig : Signature} {theory : Theory} {H K : Hyps} {p : Tm}
    (proof : Derives sig theory (H ∪ K) p)
    (premises : ∀ q ∈ H, Derives sig theory K q) : Derives sig theory K p := by
  induction H using Finset.induction_on with
  | empty => simpa using proof
  | @insert q H fresh ih =>
      have hq := premises q (Finset.mem_insert_self q H)
      have next := proof.cut hq
      have context : ((insert q H) ∪ K).erase q ∪ K = H ∪ K := by
        ext t
        by_cases h : t = q
        · subst t; simp [fresh]
        · simp [h]
      apply ih (context ▸ next)
      exact fun r hr => premises r (Finset.mem_insert_of_mem hr)

/-- Substitute derivations for every hypothesis of a theorem. -/
theorem substituteHyps {sig : Signature} {theory : Theory} {H K : Hyps} {p : Tm}
    (proof : Derives sig theory H p) (typed : TypedHyps sig [] K)
    (premises : ∀ q ∈ H, Derives sig theory K q) : Derives sig theory K p :=
  cutAll (proof.unionHyps typed) premises

/-- Enlarging the object theory preserves every derivation. -/
theorem mono_theory {sig : Signature} {theory larger : Theory}
    (included : ∀ p ∈ theory, p ∈ larger) {H : Hyps} {p : Tm}
    (proof : Derives sig theory H p) : Derives sig larger H p := by
  induction proof with
  | «axiom» member typing => exact .axiom (included _ member) typing
  | refl typing => exact .refl typing
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | mkComb _ _ ih₁ ih₂ => exact .mkComb ih₁ ih₂
  | abs name domain fresh _ ih => exact .abs name domain fresh ih
  | beta name domain typing fresh => exact .beta name domain typing fresh
  | assume typing => exact .assume typing
  | eqMp _ _ ih₁ ih₂ => exact .eqMp ih₁ ih₂
  | deductAntisym _ _ ih₁ ih₂ => exact .deductAntisym ih₁ ih₂
  | inst σ typing _ ih => exact .inst σ typing ih
  | instType σ typing _ ih => exact .instType σ typing ih

end Derives
end Silmaril.Logic.HOLLight
