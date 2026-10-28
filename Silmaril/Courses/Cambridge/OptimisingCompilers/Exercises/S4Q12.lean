module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S4Q11

/-! # Exercise sheet 4, question 12 (WebLambda examples)

Source: `cam-optcomp-2025-exercise-sheet-4` in `references.bib`, question 12.


(a) `int →^{server} int`, created on the server only: the body runs only on the
server, so by (fun) so does the λ (`example_a`).

(b) The branches meet only at `int →^∅ int` (`S4Q10.if_example`), so the
application can run nowhere: its environments are `∅` (`example_b`), and no
derivation gives a non-empty set (`example_b_nowhere`). The program is useless
although each branch alone is fine.

(c) The left operand has type `int →^∅ int` and `λx.x : int →^𝓔 int`, so `⊕`
gives `int →^𝓔 int` (`example_c`): the identity covers both sides.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S4Q12

open S4Q9 S4Q10 S4Q11

theorem example_a :
    DerivesOplus Γprim (.lam "x" (.app (.var "console.write") (.var "x")))
      (.arrow .int {.server} .int) {.server} := by
  have h : DerivesOplus Γprim (.lam "x" (.app (.var "console.write") (.var "x")))
      (.arrow .int ({.server} ∩ Set.univ ∩ Set.univ) .int) ({.server} ∩ Set.univ ∩ Set.univ) :=
    .lam (.app (t := .int) (.base (.var (by simp [Γprim])))
      (.base (.var (by simp))))
  simpa using h

theorem example_b :
    DerivesOplus Γprim
      (.app (.ite (.var "b") (.var "console.write") (.var "window.alert")) (.var "b")) .int ∅ := by
  have h : DerivesOplus Γprim
      (.app (.ite (.var "b") (.var "console.write") (.var "window.alert")) (.var "b")) .int
      (∅ ∩ Set.univ ∩ Set.univ) :=
    .app (.base if_example) (.base (.var (by simp [Γprim])))
  simpa using h

/-! ### Inversion lemmas for `example_b_nowhere` -/

theorem sub_arrow_inv {a : Ty} {E : Set Loc} {b t : Ty} (h : Sub (.arrow a E b) t) :
    ∃ a' E' b', t = .arrow a' E' b' ∧ E' ⊆ E := by
  cases h with
  | arrow _ _ hE => exact ⟨_, _, _, rfl, hE⟩

/-- A common supertype of the two primitives runs nowhere. -/
theorem branches_nowhere {t : Ty} (h₁ : Sub (.arrow .int {.server} .int) t)
    (h₂ : Sub (.arrow .int {.client} .int) t) : ∃ a E b, t = .arrow a E b ∧ E = ∅ := by
  obtain ⟨a, E, b, rfl, hE₁⟩ := sub_arrow_inv h₁
  obtain ⟨a', E', b', he, hE₂⟩ := sub_arrow_inv h₂
  cases he
  refine ⟨_, _, _, rfl, Set.subset_empty_iff.1 fun l hl => ?_⟩
  have h₁ := hE₁ hl
  have h₂ := hE₂ hl
  rw [Set.mem_singleton_iff] at h₁ h₂
  subst h₁
  cases h₂

/-- Without subsumption the conditional does not type-check at all. -/
theorem derives_ite_false {t : Ty} {E : Set Loc}
    (h : Derives Γprim (.ite (.var "b") (.var "console.write") (.var "window.alert")) t E) :
    False := by
  cases h with
  | ite _ h₁ h₂ =>
    cases h₁ with
    | var h₁ =>
      cases h₂ with
      | var h₂ =>
        have e := h₁.trans h₂.symm
        simp [Γprim] at e

theorem sub_var_inv {Γ : Ctx} {x : String} {t : Ty} {E : Set Loc}
    (h : DerivesSub Γ (.var x) t E) : ∃ t₀, Γ x = some t₀ ∧ Sub t₀ t := by
  generalize he : Term.var x = e at h
  induction h with
  | base hd => subst he; cases hd with | var h => exact ⟨_, h, Sub.refl _⟩
  | var h => cases he; exact ⟨_, h, Sub.refl _⟩
  | sub _ hs ih => obtain ⟨t₀, h₁, h₂⟩ := ih he; exact ⟨t₀, h₁, h₂.trans hs⟩
  | _ => cases he

theorem oplus_var_inv {Γ : Ctx} {x : String} {t : Ty} {E : Set Loc}
    (h : DerivesOplus Γ (.var x) t E) : ∃ t₀, Γ x = some t₀ ∧ Sub t₀ t := by
  generalize he : Term.var x = e at h
  induction h with
  | base hd => subst he; exact sub_var_inv hd
  | sub _ hs ih => obtain ⟨t₀, h₁, h₂⟩ := ih he; exact ⟨t₀, h₁, h₂.trans hs⟩
  | _ => cases he

theorem sub_ite_inv {t : Ty} {E : Set Loc}
    (h : DerivesSub Γprim (.ite (.var "b") (.var "console.write") (.var "window.alert")) t E) :
    ∃ a E₁ b, t = .arrow a E₁ b ∧ E₁ = ∅ := by
  generalize hΓ : Γprim = Γ at h
  generalize he : Term.ite (.var "b") (.var "console.write") (.var "window.alert") = e at h
  induction h with
  | base hd => subst hΓ he; exact (derives_ite_false hd).elim
  | ite _ h₁ h₂ _ _ _ =>
    cases he; subst hΓ
    obtain ⟨t₁, ht₁, hs₁⟩ := sub_var_inv h₁
    obtain ⟨t₂, ht₂, hs₂⟩ := sub_var_inv h₂
    simp [Γprim] at ht₁ ht₂
    subst ht₁ ht₂
    exact branches_nowhere hs₁ hs₂
  | sub _ hs ih =>
    obtain ⟨a, E₁, b, rfl, rfl⟩ := ih hΓ he
    obtain ⟨a', E', b', rfl, hE⟩ := sub_arrow_inv hs
    exact ⟨a', E', b', rfl, Set.subset_empty_iff.1 hE⟩
  | _ => cases he

theorem oplus_ite_inv {t : Ty} {E : Set Loc}
    (h : DerivesOplus Γprim (.ite (.var "b") (.var "console.write") (.var "window.alert")) t E) :
    ∃ a E₁ b, t = .arrow a E₁ b ∧ E₁ = ∅ := by
  generalize hΓ : Γprim = Γ at h
  generalize he : Term.ite (.var "b") (.var "console.write") (.var "window.alert") = e at h
  induction h with
  | base hd => subst hΓ he; exact sub_ite_inv hd
  | ite _ h₁ h₂ _ _ _ =>
    cases he; subst hΓ
    obtain ⟨t₁, ht₁, hs₁⟩ := oplus_var_inv h₁
    obtain ⟨t₂, ht₂, hs₂⟩ := oplus_var_inv h₂
    simp [Γprim] at ht₁ ht₂
    subst ht₁ ht₂
    exact branches_nowhere hs₁ hs₂
  | sub _ hs ih =>
    obtain ⟨a, E₁, b, rfl, rfl⟩ := ih hΓ he
    obtain ⟨a', E', b', rfl, hE⟩ := sub_arrow_inv hs
    exact ⟨a', E', b', rfl, Set.subset_empty_iff.1 hE⟩
  | _ => cases he

theorem sub_app_inv {t : Ty} {E : Set Loc}
    (h : DerivesSub Γprim
      (.app (.ite (.var "b") (.var "console.write") (.var "window.alert")) (.var "b")) t E) :
    E = ∅ := by
  generalize hΓ : Γprim = Γ at h
  generalize he : Term.app (.ite (.var "b") (.var "console.write") (.var "window.alert"))
    (.var "b") = e at h
  induction h with
  | base hd =>
    subst hΓ he
    cases hd with | app hf _ => exact (derives_ite_false hf).elim
  | app hf _ _ _ =>
    cases he; subst hΓ
    obtain ⟨a, E₁, b, h₁, rfl⟩ := sub_ite_inv hf
    cases h₁
    simp
  | sub _ _ ih => exact ih hΓ he
  | _ => cases he

theorem example_b_nowhere {E : Set Loc}
    (h : DerivesOplus Γprim
      (.app (.ite (.var "b") (.var "console.write") (.var "window.alert")) (.var "b")) .int E) :
    E = ∅ := by
  generalize hΓ : Γprim = Γ at h
  generalize ht : Ty.int = t at h
  generalize he : Term.app (.ite (.var "b") (.var "console.write") (.var "window.alert"))
    (.var "b") = e at h
  induction h with
  | base hd => subst hΓ he; exact sub_app_inv hd
  | app hf _ _ _ =>
    cases he; subst hΓ
    obtain ⟨a, E₁, b, h₁, rfl⟩ := oplus_ite_inv hf
    cases h₁
    simp
  | sub _ hs ih => subst ht; cases hs; exact ih hΓ rfl he
  | _ => cases he

theorem example_c :
    DerivesOplus Γprim
      (.oplus (.ite (.var "b") (.var "console.write") (.var "window.alert")) (.lam "x" (.var "x")))
      (.arrow .int Set.univ .int) Set.univ := by
  have h : DerivesOplus Γprim
      (.oplus (.ite (.var "b") (.var "console.write") (.var "window.alert")) (.lam "x" (.var "x")))
      (.arrow .int (∅ ∪ Set.univ) .int) Set.univ :=
    .oplus (.base if_example) (.lam (.base (.var (by simp))))
  simpa using h

end Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S4Q12
