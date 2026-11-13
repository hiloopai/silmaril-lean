module

public import Silmaril.X86.Concurrency.Cir.Fj.Defs

/-!
# Fork-join CIR: the footprint check is sound

`Par.okB = true → Par.Ok`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Fj

open Silmaril.X86.Concurrency.Cir.Fj

theorem pairwiseB_sound {r : Nat × Nat → Nat × Nat → Bool} :
    ∀ {l : List (Nat × Nat)}, Par.okB.pairwiseB r l = true → l.Pairwise fun c d => r c d = true
  | [], _ => List.Pairwise.nil
  | c :: l, h => by
    simp only [Par.okB.pairwiseB, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (pairwiseB_sound h.2)

theorem ok_of_okB {F : Par} (h : F.okB = true) : F.Ok := by
  simp only [Par.okB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, pairwiseB_sound h5, h6⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Fj
