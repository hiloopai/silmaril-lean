module

public import Silmaril.Calculi.LambdaCube.PTSConfluence

@[expose] public section

set_option autoImplicit true

/-! # Conversion metatheory for the cube's pseudo-terms

Consequences of Church–Rosser (`Pseudo.Conv.join`) used by the generation
arguments over encoded telescopes:

* `Pseudo.Conv` coincides with joinability by parallel reduction
  (`Pseudo.conv_iff_joinable`);
* conversion is closed under renaming and substitution
  (`Pseudo.Conv.rename`, `Pseudo.Conv.subst`, `Pseudo.Conv.substOne_left`);
* products are injective up to conversion against redex-free terms
  (`Pseudo.Conv.pi_noRedex`), and distinct sorts are not convertible
  (`Pseudo.Conv.sort_inj`).
-/

namespace Silmaril.Calculi.LambdaCube

namespace Pseudo

variable {S : Type}

theorem Conv.of_eq {t u : Pseudo S} (h : t = u) : Conv t u := h ▸ .refl t

theorem Conv.trans_eq {t u v : Pseudo S} (h : Conv t u) (e : u = v) : Conv t v := e ▸ h

/-- Parallel reduction is contained in conversion. -/
theorem Par.toConv {t u : Pseudo S} (h : Par t u) : Conv t u := by
  induction h with
  | sort s => exact .refl _
  | var n => exact .refl _
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | pi _ _ ih₁ ih₂ => exact .pi ih₁ ih₂
  | beta A _ _ ih₁ ih₂ => exact (Conv.app (Conv.lam (.refl A) ih₁) ih₂).trans (.beta A _ _)

theorem reflTransGen_par_toConv {t u : Pseudo S}
    (h : Relation.ReflTransGen (Par (S := S)) t u) : Conv t u := by
  induction h with
  | refl => exact .refl _
  | tail _ hp ih => exact ih.trans hp.toConv

theorem Joinable.toConv {t u : Pseudo S} (h : Joinable t u) : Conv t u := by
  obtain ⟨v, h₁, h₂⟩ := h
  exact (reflTransGen_par_toConv h₁).trans (reflTransGen_par_toConv h₂).symm

/-- Conversion is joinability by parallel reduction. -/
theorem conv_iff_joinable {t u : Pseudo S} : Conv t u ↔ Joinable t u :=
  ⟨Conv.join, Joinable.toConv⟩

/-- Any operation compatible with parallel reduction preserves conversion. -/
theorem Conv.map (g : Pseudo S → Pseudo S) (hg : ∀ x y, Par x y → Par (g x) (g y))
    {t u : Pseudo S} (h : Conv t u) : Conv (g t) (g u) := by
  obtain ⟨v, h₁, h₂⟩ := h.join
  exact Joinable.toConv ⟨g v, reflTransGen_par_map g hg h₁, reflTransGen_par_map g hg h₂⟩

theorem Conv.rename {t u : Pseudo S} (h : Conv t u) (r : ℕ → ℕ) :
    Conv (t.rename r) (u.rename r) :=
  h.map (Pseudo.rename r) (fun _ _ hp => hp.rename r)

theorem Conv.subst {t u : Pseudo S} (h : Conv t u) (σ : ℕ → Pseudo S) :
    Conv (t.subst σ) (u.subst σ) :=
  h.map (Pseudo.subst σ) (fun _ _ hp => hp.subst σ σ (fun _ => Par.refl _))

theorem Conv.substOne_left {b b' : Pseudo S} (h : Conv b b') (a : Pseudo S) :
    Conv (b.substOne a) (b'.substOne a) := by
  unfold substOne
  exact h.subst _

/-- Parallel reduction sequences from a product stay products. -/
theorem reflTransGen_par_pi_inv {A B v : Pseudo S}
    (h : Relation.ReflTransGen (Par (S := S)) (.pi A B) v) :
    ∃ A' B', v = .pi A' B' ∧ Relation.ReflTransGen Par A A' ∧
      Relation.ReflTransGen Par B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ hp ih =>
    obtain ⟨A', B', rfl, hA, hB⟩ := ih
    cases hp with
    | pi h₁ h₂ => exact ⟨_, _, rfl, hA.tail h₁, hB.tail h₂⟩

/-- A redex-free term convertible to a product is a product with convertible
components. -/
theorem Conv.pi_noRedex {A B C : Pseudo S} (h : Conv (.pi A B) C) (hC : NoRedex C) :
    ∃ A' B', C = .pi A' B' ∧ Conv A A' ∧ Conv B B' := by
  obtain ⟨v, h₁, h₂⟩ := h.join
  have hv := reflTransGen_par_eq_of_noRedex h₂ hC
  subst hv
  obtain ⟨A', B', rfl, hA, hB⟩ := reflTransGen_par_pi_inv h₁
  exact ⟨A', B', rfl, reflTransGen_par_toConv hA, reflTransGen_par_toConv hB⟩

/-- Distinct sorts are not convertible. -/
theorem Conv.sort_inj {s s' : S} (h : Conv (Pseudo.sort s) (.sort s')) : s = s' := by
  have e := h.eq_of_noRedex trivial trivial
  cases e
  rfl

end Pseudo

end Silmaril.Calculi.LambdaCube
