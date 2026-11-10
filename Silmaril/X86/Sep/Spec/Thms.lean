module

public import Silmaril.X86.Sep.Spec.Defs
public import Silmaril.X86.Sep.Thms
public import Silmaril.X86.Extends.Thms
import Silmaril.Proofs.X86.Sep.Bridge
import Silmaril.Proofs.X86.Sep.Rules

/-!
# Rules for `Triple` and `SPEC`

* Structural rules: `Triple.frame` (by associativity alone), `Triple.conseq`, `Triple.pre`,
  `Triple.post`, `Triple.trans` (sequencing), `Triple.refl`, `Triple.sexists`,
  `Triple.spure`; the same for `SPEC`, plus `SPEC.code_frame` (more code may be present).
* `Triple.of_local`: **a triple from a run** that leaves every location outside the
  precondition's fragment unchanged, and whose final state satisfies the postcondition on
  that fragment (`Frag.reval`). Machine proofs enter the logic through it.
* `Triple.run`, `Triple.holds`: **a run from a triple.** If the precondition holds of part
  of a live state, the machine reaches a state where the postcondition holds of part of it
  and every other location is unchanged.
* `Triple.lift`, `SPEC.lift`: **a triple of `I` is a triple of every machine extending
  `I`** (`SegVC.Isa.Extends`; `frag_view`: an extension's state has the fragment of its
  view). With `Open9.extendsOpen` and `Str9.extendsOpen9`, triples move up the tower.
-/

@[expose] public section

namespace Silmaril.X86.Sep

open Silmaril.X86 (MState)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (Reaches)
open Frag (union Disjoint Le reval)

variable {σ τ : Type} {I : Isa σ} {P Q R P' Q' C D : SProp}

theorem frag_isSome (s : σ) (l : Loc) : (frag I s l).isSome := toFrag_isSome _ l

/-- An extension's state has the fragment of its view. -/
theorem frag_view {J : Isa τ} (E : I.Extends J) (x : τ) : frag J x = frag I (E.view x) :=
  Silmaril.Proofs.X86.Sep.frag_view E x

/-! ## Triples -/

/-- **The frame rule.** -/
theorem Triple.frame (h : Triple I P Q) (R : SProp) : Triple I (P ∗ R) (Q ∗ R) :=
  Silmaril.Proofs.X86.Sep.triple_frame h R

/-- **Consequence.** -/
theorem Triple.conseq (hp : P' ⊢ₛ P) (h : Triple I P Q) (hq : Q ⊢ₛ Q') : Triple I P' Q' := by
  intro F m hl hm
  obtain ⟨m', hr, hQ⟩ := h F m hl (sep_mono_left F hp _ hm)
  exact ⟨m', hr, sep_mono_left F hq _ hQ⟩

theorem Triple.pre (hp : P' ⊢ₛ P) (h : Triple I P Q) : Triple I P' Q :=
  Triple.conseq hp h (entails_refl Q)

theorem Triple.post (h : Triple I P Q) (hq : Q ⊢ₛ Q') : Triple I P Q' :=
  Triple.conseq (entails_refl P) h hq

/-- **Sequencing.** -/
theorem Triple.trans (h₁ : Triple I P Q) (h₂ : Triple I Q R) : Triple I P R :=
  Silmaril.Proofs.X86.Sep.triple_trans h₁ h₂

/-- The empty run. -/
theorem Triple.refl (P : SProp) : Triple I P P :=
  fun _ m _ hm => ⟨m, Reaches.refl _ m, hm⟩

/-- **Existential precondition.** -/
theorem Triple.sexists {α : Sort _} {P : α → SProp} (h : ∀ x, Triple I (P x) Q) :
    Triple I (sexists P) Q :=
  Silmaril.Proofs.X86.Sep.triple_sexists h

/-- **Pure precondition.** -/
theorem Triple.spure {φ : Prop} (h : φ → Triple I P Q) : Triple I (⌜φ⌝ ∗ P) Q :=
  Silmaril.Proofs.X86.Sep.triple_spure h

/-- **A triple from a run** that changes nothing outside the precondition's fragment. -/
theorem Triple.of_local
    (h : ∀ s h₁, I.live s → P h₁ → Le h₁ (frag I s) →
      ∃ t, Reaches I.step s t ∧
        (∀ l, h₁ l = none → frag I t l = frag I s l) ∧ Q (reval h₁ (frag I t))) :
    Triple I P Q :=
  Silmaril.Proofs.X86.Sep.triple_of_local h

/-- **A run from a triple**: only the precondition's locations may change. -/
theorem Triple.run (h : Triple I P Q) {h₁ : Frag} {s : σ} (hlive : I.live s) (hp : P h₁)
    (hl : Le h₁ (frag I s)) :
    ∃ t h₁', Reaches I.step s t ∧ Q h₁' ∧ Le h₁' (frag I t) ∧
      ∀ l, h₁ l = none → frag I t l = frag I s l :=
  Silmaril.Proofs.X86.Sep.triple_run h hlive hp hl

theorem Triple.holds (h : Triple I P Q) {s : σ} (hlive : I.live s)
    (hp : Holds P ⟨I.core s, I.mem s⟩) :
    ∃ t, Reaches I.step s t ∧ Holds Q ⟨I.core t, I.mem t⟩ := by
  obtain ⟨h₁, hp, hl⟩ := hp
  obtain ⟨t, h₁', hr, hq, hl', -⟩ := h.run hlive hp hl
  exact ⟨t, hr, h₁', hq, hl'⟩

/-- **A triple of `I` is a triple of every machine extending `I`.** -/
theorem Triple.lift {J : Isa τ} (E : I.Extends J) (h : Triple I P Q) : Triple J P Q :=
  Silmaril.Proofs.X86.Sep.triple_lift E h

/-! ## `SPEC` -/

theorem SPEC.frame (h : SPEC I C P Q) (R : SProp) : SPEC I C (P ∗ R) (Q ∗ R) := by
  have := Triple.frame h R
  unfold SPEC
  rwa [sep_assoc, sep_assoc] at this

theorem SPEC.conseq (hp : P' ⊢ₛ P) (h : SPEC I C P Q) (hq : Q ⊢ₛ Q') : SPEC I C P' Q' :=
  Triple.conseq (sep_mono_right C hp) h (sep_mono_right C hq)

theorem SPEC.trans (h₁ : SPEC I C P Q) (h₂ : SPEC I C Q R) : SPEC I C P R := Triple.trans h₁ h₂

theorem SPEC.sexists {α : Sort _} {P : α → SProp} (h : ∀ x, SPEC I C (P x) Q) :
    SPEC I C (sexists P) Q := by
  unfold SPEC
  rw [sep_sexists]
  exact Triple.sexists h

theorem SPEC.spure {φ : Prop} (h : φ → SPEC I C P Q) : SPEC I C (⌜φ⌝ ∗ P) Q := by
  unfold SPEC
  rw [sep_left_comm]
  exact Triple.spure h

/-- More code may be present. -/
theorem SPEC.code_frame (h : SPEC I C P Q) (D : SProp) : SPEC I (C ∗ D) P Q :=
  Silmaril.Proofs.X86.Sep.spec_code_frame h D

theorem SPEC.code_comm (h : SPEC I (C ∗ D) P Q) : SPEC I (D ∗ C) P Q := by
  rwa [sep_comm D C]

theorem SPEC.lift {J : Isa τ} (E : I.Extends J) (h : SPEC I C P Q) : SPEC J C P Q :=
  Triple.lift E h

end Silmaril.X86.Sep
