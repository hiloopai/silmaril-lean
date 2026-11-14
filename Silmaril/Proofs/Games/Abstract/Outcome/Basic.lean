module

public import Silmaril.Games.Abstract.Outcome.Defs
public import Silmaril.Games.Abstract.Machine.Thms

/-!
# Outcome-tagged traces: proofs

The run tag is the trace; every tagged observation's trace is a trace; the
fibres of `collapse`; the chain tagged ⇒ coarse ⇒ trace equivalence; the exact
characterisation of coarse equivalence; and soundness and completeness of
may/must testing for saturated, separating context classes.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.Outcome

open Silmaril.Games.Abstract Silmaril.Games.Abstract.OMachine

universe u

variable {G : Game.{u}} {R : Type u} {M N : OMachine G R}

theorem mem_obs_fin {s : List G.Move} {t : Tag R} :
    Obs.fin s t ∈ M.obs ↔ ∃ y, M.Run M.init s y ∧ M.Shows y t :=
  ⟨fun h => by cases h with | fin y h₁ h₂ => exact ⟨y, h₁, h₂⟩,
    fun ⟨y, h₁, h₂⟩ => .fin y h₁ h₂⟩

theorem fin_run_mem_iff {s : List G.Move} : Obs.fin s .run ∈ M.obs ↔ s ∈ M.traces := by
  rw [mem_obs_fin]
  exact ⟨fun ⟨y, h, _⟩ => ⟨y, h⟩, fun ⟨y, h⟩ => ⟨y, h, trivial⟩⟩

theorem mem_traces_of_fin {s : List G.Move} {t : Tag R} (h : Obs.fin s t ∈ M.obs) :
    s ∈ M.traces := by
  obtain ⟨y, h, -⟩ := mem_obs_fin.1 h
  exact ⟨y, h⟩

theorem collapse_eq_iff {o o' : Obs G R} :
    o.collapse = o'.collapse ↔ o = o' ∨ ∃ s, Obs.IsAbortAt s o ∧ Obs.IsAbortAt s o' := by
  constructor
  · intro h
    rcases o with ⟨s, t⟩ | ω <;> rcases o' with ⟨s', t'⟩ | ω' <;>
      simp only [Obs.collapse, CObs.fin.injEq, CObs.inf.injEq, reduceCtorEq] at h
    · obtain ⟨rfl, h⟩ := h
      cases t <;> cases t' <;> simp_all [Tag.collapse, Obs.IsAbortAt]
    · exact .inl (h ▸ rfl)
  · rintro (rfl | ⟨s, rfl | rfl, rfl | rfl⟩) <;> rfl

theorem not_abort_eq {o o' : Obs G R} (ho : ∀ s, ¬ Obs.IsAbortAt s o) (h : o.collapse = o'.collapse) :
    o' = o := by
  rcases collapse_eq_iff.1 h with rfl | ⟨s, h₁, -⟩
  · rfl
  · exact absurd h₁ (ho s)

theorem cobs_mono (h : M.obs ⊆ N.obs) : M.cobs ⊆ N.cobs := Set.image_mono h

theorem traces_subset_of_cobs (h : M.cobs ⊆ N.cobs) : M.traces ⊆ N.traces := by
  intro s hs
  obtain ⟨o, ho, he⟩ := h ⟨_, fin_run_mem_iff.2 hs, rfl⟩
  have : o = .fin s .run :=
    not_abort_eq (o := .fin s .run) (fun s' h => by rcases h with h | h <;> cases h) he.symm
  exact fin_run_mem_iff.1 (this ▸ ho)

theorem cobs_subset_of {M N : OMachine G R}
    (h₁ : ∀ o, (∀ s, ¬ Obs.IsAbortAt s o) → o ∈ M.obs → o ∈ N.obs)
    (h₂ : ∀ s, (Obs.fin s .trap ∈ M.obs ∨ Obs.fin s .div ∈ M.obs) →
      (Obs.fin s .trap ∈ N.obs ∨ Obs.fin s .div ∈ N.obs)) : M.cobs ⊆ N.cobs := by
  rintro _ ⟨o, ho, rfl⟩
  by_cases ha : ∃ s, Obs.IsAbortAt s o
  · obtain ⟨s, hs⟩ := ha
    rcases h₂ s (by rcases hs with rfl | rfl <;> simp_all) with h | h
    · exact ⟨_, h, collapse_eq_iff.2 (.inr ⟨s, .inl rfl, hs⟩)⟩
    · exact ⟨_, h, collapse_eq_iff.2 (.inr ⟨s, .inr rfl, hs⟩)⟩
  · push Not at ha
    exact ⟨o, h₁ o ha ho, rfl⟩

theorem coarseEquiv_iff :
    M.CoarseEquiv N ↔ (∀ o, (∀ s, ¬ Obs.IsAbortAt s o) → (o ∈ M.obs ↔ o ∈ N.obs)) ∧
      ∀ s, (Obs.fin s .trap ∈ M.obs ∨ Obs.fin s .div ∈ M.obs ↔
        Obs.fin s .trap ∈ N.obs ∨ Obs.fin s .div ∈ N.obs) := by
  constructor
  · intro h
    have sub : ∀ {A B : OMachine G R}, A.cobs = B.cobs →
        (∀ o, (∀ s, ¬ Obs.IsAbortAt s o) → o ∈ A.obs → o ∈ B.obs) ∧
        ∀ s, (Obs.fin s .trap ∈ A.obs ∨ Obs.fin s .div ∈ A.obs) →
          (Obs.fin s .trap ∈ B.obs ∨ Obs.fin s .div ∈ B.obs) := by
      intro A B hAB
      refine ⟨fun o ho hA => ?_, fun s hs => ?_⟩
      · obtain ⟨o', ho', he⟩ : o.collapse ∈ B.cobs := hAB ▸ ⟨o, hA, rfl⟩
        exact not_abort_eq ho he.symm ▸ ho'
      · have key : CObs.fin s .abort ∈ B.cobs := hAB ▸ (by
          rcases hs with hs | hs
          · exact ⟨_, hs, rfl⟩
          · exact ⟨_, hs, rfl⟩)
        obtain ⟨o', ho', he⟩ := key
        rcases o' with ⟨s', t'⟩ | ω <;> simp only [Obs.collapse, CObs.fin.injEq, reduceCtorEq] at he
        obtain ⟨rfl, he⟩ := he
        cases t' <;> simp_all [Tag.collapse]
    exact ⟨fun o ho => ⟨(sub h).1 o ho, (sub h.symm).1 o ho⟩,
      fun s => ⟨(sub h).2 s, (sub h.symm).2 s⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact Set.Subset.antisymm (cobs_subset_of (fun o ho => (h₁ o ho).1) (fun s => (h₂ s).1))
      (cobs_subset_of (fun o ho => (h₁ o ho).2) (fun s => (h₂ s).2))

/-! ## Testing over observations -/

variable {α β : Type u}

theorem may_sound {X : ObsTests α} {κ : α → β} (hX : X.Saturated κ) {A B : Set α}
    (h : κ '' A = κ '' B) : X.MayEquiv A B := by
  have one : ∀ {A B : Set α}, κ '' A ⊆ κ '' B → ∀ c, X.MayPass c A → X.MayPass c B := by
    intro A B hAB c ⟨o, hoA, hoc⟩
    obtain ⟨o', ho', he⟩ := hAB ⟨o, hoA, rfl⟩
    exact ⟨o', ho', (hX c o' o he).2 hoc⟩
  exact fun c => ⟨one h.le c, one h.ge c⟩

theorem must_sound {X : ObsTests α} {κ : α → β} {complete : α → Prop} (hX : X.Saturated κ)
    (hc : ∀ o o', κ o = κ o' → (complete o ↔ complete o')) {A B : Set α}
    (h : κ '' A = κ '' B) : X.MustEquiv complete A B := by
  have one : ∀ {A B : Set α}, κ '' B ⊆ κ '' A → ∀ c,
      X.MustPass complete c A → X.MustPass complete c B := by
    intro A B hBA c hA o hoB hco
    obtain ⟨o', ho', he⟩ := hBA ⟨o, hoB, rfl⟩
    exact (hX c o' o he).1 (hA o' ho' ((hc o' o he).2 hco))
  exact fun c => ⟨one h.ge c, one h.le c⟩

theorem may_complete {X : ObsTests α} {κ : α → β} (hX : X.Separates κ) {A B : Set α}
    (h : X.MayEquiv A B) : κ '' A = κ '' B := by
  ext b
  obtain ⟨c, hc⟩ := hX b
  have e : ∀ C : Set α, X.MayPass c C ↔ b ∈ κ '' C := fun C =>
    ⟨fun ⟨o, ho, hoc⟩ => ⟨o, ho, (hc o).1 hoc⟩, fun ⟨o, ho, he⟩ => ⟨o, ho, (hc o).2 he⟩⟩
  rw [← e, ← e]
  exact h c

end Silmaril.Proofs.Games.Abstract.Outcome
