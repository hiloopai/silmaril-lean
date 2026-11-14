module

public import Silmaril.Servers.Observe.Defs

/-!
# Proofs: observations after initialization
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Observe

open Silmaril.Servers Silmaril.Servers.Observe

variable {A : Sig}

theorem initSafe_withInit (M : Model A) : (Beh.withInit False M).InitSafe := by
  rintro o (⟨_, h⟩ | ⟨t, rfl, _⟩)
  · exact h.elim
  · exact fun h => by cases h

theorem must_sen_iff {B : Beh A} (hB : B.Healthy) (φ : Sen A) :
    B.Must (Obs.sen φ) ↔ B.traces.Sat φ := by
  constructor
  · exact fun h t ht => h _ ht
  · intro h o ho
    cases o with
    | initFail => trivial
    | run t => exact h t ho
    | stop t => exact h t (hB.2 t ho)

end Silmaril.Proofs.Servers.Observe
