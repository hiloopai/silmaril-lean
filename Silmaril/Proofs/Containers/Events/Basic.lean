module

public import Silmaril.Containers.Events.Defs

public section
namespace Silmaril.Proofs.Containers.Events
open Silmaril.Containers
variable {S B : Type}

theorem trace_embed (v : EventCodec S B) (t : List S) :
    v.trace (t.map v.embed) = .ok t := by
  induction t with
  | nil => rfl
  | cons e es ih => simp [EventCodec.trace, v.roundtrip, ih]

theorem expand_restrict (v : EventCodec S B) (M : Model B)
    (h : M.Sat v.Confined) (b : Beh B) : v.expand (v.restrict M) b ↔ M b := by
  constructor
  · rintro ⟨s, hs, rfl⟩; exact hs
  · intro hb
    obtain ⟨s, rfl⟩ := h b hb
    exact ⟨s, hb, rfl⟩

theorem finite_noUB_iff (v : EventCodec S B) (t : List B) (stop : Stop) :
    Spec.noUB (v.finite t stop) ↔
      (∃ ss, v.trace t = .ok ss) ∧ Spec.noUB (.done t stop) := by
  cases h : v.trace t with
  | ok ss => cases stop <;> simp [EventCodec.finite, h, Spec.noUB]
  | error pre => simp [EventCodec.finite, h, Spec.noUB]

end Silmaril.Proofs.Containers.Events
