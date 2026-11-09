module

public import Silmaril.X86.Sep.Spec.Defs
public import Silmaril.X86.Sep.Thms

/-!
# Proofs: structural rules of `Triple` and `SPEC`

Behind `Silmaril/X86/Sep/Spec/Thms.lean`: the frame rule (by associativity alone),
sequencing (liveness carries along the first run), existential and pure preconditions, and
the code frame of `SPEC`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep

open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep

variable {σ : Type} {I : Isa σ} {P Q R C : SProp}

theorem triple_frame (h : Triple I P Q) (R : SProp) : Triple I (P ∗ R) (Q ∗ R) := by
  intro F m hl hm
  rw [sep_assoc] at hm
  obtain ⟨m', hr, hq⟩ := h (R ∗ F) m hl hm
  exact ⟨m', hr, by rw [sep_assoc]; exact hq⟩

theorem triple_trans (h₁ : Triple I P Q) (h₂ : Triple I Q R) : Triple I P R := by
  intro F m hl hm
  obtain ⟨m', hr, hq⟩ := h₁ F m hl hm
  obtain ⟨m'', hr', hR⟩ := h₂ F m' (Silmaril.X86.SegVC.live_reaches hl hr) hq
  exact ⟨m'', hr.trans hr', hR⟩

theorem triple_sexists {α : Sort _} {P : α → SProp} (h : ∀ x, Triple I (P x) Q) :
    Triple I (sexists P) Q := by
  intro F m hl hm
  rw [sexists_sep] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x F m hl hx

theorem triple_spure {φ : Prop} (h : φ → Triple I P Q) : Triple I (⌜φ⌝ ∗ P) Q := by
  intro F m hl hm
  rw [sep_assoc, spure_sep_apply] at hm
  exact h hm.1 F m hl hm.2

theorem spec_code_frame (h : SPEC I C P Q) (D : SProp) : SPEC I (C ∗ D) P Q := by
  have := triple_frame h D
  unfold SPEC
  have e₁ : ((C ∗ D) ∗ P) = ((C ∗ P) ∗ D) := by ac_rfl
  have e₂ : ((C ∗ D) ∗ Q) = ((C ∗ Q) ∗ D) := by ac_rfl
  rw [e₁, e₂]; exact this

end Silmaril.Proofs.X86.Sep
