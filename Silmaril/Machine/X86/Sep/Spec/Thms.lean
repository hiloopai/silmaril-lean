module

public import Silmaril.Machine.X86.Sep.Spec.Defs
public import Silmaril.Machine.X86.Sep.Thms
import Silmaril.Proofs.Machine.X86.Sep.Bridge

/-!
# Rules for `Triple` and `SPEC`

* Structural rules: `Triple.frame` (by associativity alone), `Triple.conseq`,
  `Triple.trans` (sequencing), `Triple.refl`, `Triple.sexists`, `Triple.spure`; the same for
  `SPEC`, plus `SPEC.code_frame` (more code may be present).
* `Triple.of_local`: **a triple from a run** that leaves every location outside the
  precondition's fragment unchanged, and whose final state satisfies the postcondition on
  that fragment (`Frag.reval`). Every existing machine proof enters the logic through it.
* `Triple.run`, `Triple.holds`: **a run from a triple.** If the precondition holds of part
  of a state, the open machine reaches a state where the postcondition holds of part of it
  and every other location is unchanged (`SPEC_to_mayChange` in DESIGN §9 terms: the
  locations of the precondition's fragment are the only ones that may change).
-/

@[expose] public section

namespace Silmaril.Machine.X86.Sep

open Silmaril.X86 (MState)
open Silmaril.Machine.Execution (Reaches)
open Frag (union Disjoint Le reval)

variable {P Q R P' Q' C D : SProp}

/-! ## Triples -/

/-- **The frame rule.** -/
theorem Triple.frame (h : Triple P Q) (R : SProp) : Triple (P ∗ R) (Q ∗ R) := by
  intro F m hm
  rw [sep_assoc] at hm
  obtain ⟨m', hr, hq⟩ := h (R ∗ F) m hm
  exact ⟨m', hr, by rw [sep_assoc]; exact hq⟩

/-- **Consequence.** -/
theorem Triple.conseq (hp : P' ⊢ₛ P) (h : Triple P Q) (hq : Q ⊢ₛ Q') : Triple P' Q' := by
  intro F m hm
  obtain ⟨m', hr, hQ⟩ := h F m (sep_mono_left F hp _ hm)
  exact ⟨m', hr, sep_mono_left F hq _ hQ⟩

theorem Triple.pre (hp : P' ⊢ₛ P) (h : Triple P Q) : Triple P' Q :=
  Triple.conseq hp h (entails_refl Q)

theorem Triple.post (h : Triple P Q) (hq : Q ⊢ₛ Q') : Triple P Q' :=
  Triple.conseq (entails_refl P) h hq

/-- **Sequencing.** -/
theorem Triple.trans (h₁ : Triple P Q) (h₂ : Triple Q R) : Triple P R := by
  intro F m hm
  obtain ⟨m', hr, hq⟩ := h₁ F m hm
  obtain ⟨m'', hr', hR⟩ := h₂ F m' hq
  exact ⟨m'', hr.trans hr', hR⟩

/-- The empty run. -/
theorem Triple.refl (P : SProp) : Triple P P :=
  fun _ m hm => ⟨m, Reaches.refl _ m, hm⟩

/-- **Existential precondition.** -/
theorem Triple.sexists {α : Sort _} {P : α → SProp} (h : ∀ x, Triple (P x) Q) :
    Triple (sexists P) Q := by
  intro F m hm
  rw [sexists_sep] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x F m hx

/-- **Pure precondition.** -/
theorem Triple.spure {φ : Prop} (h : φ → Triple P Q) : Triple (⌜φ⌝ ∗ P) Q := by
  intro F m hm
  rw [sep_assoc, spure_sep_apply] at hm
  exact h hm.1 F m hm.2

/-- **A triple from a run** that changes nothing outside the precondition's fragment. -/
theorem Triple.of_local
    (h : ∀ m h₁, P h₁ → Le h₁ (toFrag m) →
      ∃ m', Reaches Silmaril.Machine.X86.Open.step m m' ∧
        (∀ l, h₁ l = none → toFrag m' l = toFrag m l) ∧ Q (reval h₁ (toFrag m'))) :
    Triple P Q :=
  Silmaril.Proofs.Machine.X86.Sep.triple_of_local h

/-- **A run from a triple**: only the precondition's locations may change. -/
theorem Triple.run (h : Triple P Q) {h₁ : Frag} {m : MState} (hp : P h₁)
    (hl : Le h₁ (toFrag m)) :
    ∃ m' h₁', Reaches Silmaril.Machine.X86.Open.step m m' ∧ Q h₁' ∧ Le h₁' (toFrag m') ∧
      ∀ l, h₁ l = none → toFrag m' l = toFrag m l :=
  Silmaril.Proofs.Machine.X86.Sep.triple_run h hp hl

theorem Triple.holds (h : Triple P Q) {m : MState} (hp : Holds P m) :
    ∃ m', Reaches Silmaril.Machine.X86.Open.step m m' ∧ Holds Q m' := by
  obtain ⟨h₁, hp, hl⟩ := hp
  obtain ⟨m', h₁', hr, hq, hl', -⟩ := h.run hp hl
  exact ⟨m', hr, h₁', hq, hl'⟩

/-! ## `SPEC` -/

theorem SPEC.frame (h : SPEC C P Q) (R : SProp) : SPEC C (P ∗ R) (Q ∗ R) := by
  have := Triple.frame h R
  unfold SPEC
  rwa [sep_assoc, sep_assoc] at this

theorem SPEC.conseq (hp : P' ⊢ₛ P) (h : SPEC C P Q) (hq : Q ⊢ₛ Q') : SPEC C P' Q' :=
  Triple.conseq (sep_mono_right C hp) h (sep_mono_right C hq)

theorem SPEC.trans (h₁ : SPEC C P Q) (h₂ : SPEC C Q R) : SPEC C P R := Triple.trans h₁ h₂

theorem SPEC.sexists {α : Sort _} {P : α → SProp} (h : ∀ x, SPEC C (P x) Q) :
    SPEC C (sexists P) Q := by
  unfold SPEC
  rw [sep_sexists]
  exact Triple.sexists h

theorem SPEC.spure {φ : Prop} (h : φ → SPEC C P Q) : SPEC C (⌜φ⌝ ∗ P) Q := by
  unfold SPEC
  rw [sep_left_comm]
  exact Triple.spure h

/-- More code may be present. -/
theorem SPEC.code_frame (h : SPEC C P Q) (D : SProp) : SPEC (C ∗ D) P Q := by
  have := Triple.frame h D
  unfold SPEC
  have e₁ : ((C ∗ D) ∗ P) = ((C ∗ P) ∗ D) := by ac_rfl
  have e₂ : ((C ∗ D) ∗ Q) = ((C ∗ Q) ∗ D) := by ac_rfl
  rw [e₁, e₂]; exact this

theorem SPEC.code_comm (h : SPEC (C ∗ D) P Q) : SPEC (D ∗ C) P Q := by
  rwa [sep_comm D C]

end Silmaril.Machine.X86.Sep
