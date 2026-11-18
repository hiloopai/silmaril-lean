module

public import Silmaril.ProofFormats.Alethe.Defs
public import Silmaril.Logic.Consequence.Resolution.Thms

/-!
# Proofs for Alethe refutations
-/

@[expose] public section

namespace Silmaril.Proofs.ProofFormats.Alethe

open Silmaril.ProofFormats.Alethe Silmaril.Consequence Silmaril.Consequence.Resolution
open Silmaril.Logic.Smt (SE)

theorem finish_sound {a φs : List SE} {ls : List (Line Rule Clause)} (h : finish a ls = .ok φs) :
    φs = a ∧ system.derives (a.map ([·])) [] := by
  unfold finish at h
  split at h
  · next hc =>
    split at h
    · next hl =>
      cases h
      refine ⟨rfl, ?_⟩
      rw [← DerivationSystem.linearDerives_eq]
      exact ⟨ls, DerivationSystem.checkLines_iff.1 hc, hl⟩
    · cases h
  · cases h

theorem checkRefutation_sound {problem proof : List UInt8} {φs : List SE}
    (h : checkRefutation problem proof = .ok φs) : ¬ ∃ v : SE → Prop, ∀ φ ∈ φs, Holds v φ := by
  simp only [checkRefutation, bind, Except.bind] at h
  split at h
  · cases h
  · next r _ =>
    obtain ⟨rfl, hd⟩ := finish_sound h
    exact refutes_units hd

end Silmaril.Proofs.ProofFormats.Alethe
