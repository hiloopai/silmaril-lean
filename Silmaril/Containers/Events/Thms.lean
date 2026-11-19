module

public import Silmaril.Containers.Events.Defs
import Silmaril.Proofs.Containers.Events.Basic

public section
namespace Silmaril.Containers.EventCodec
variable {S B : Type}

theorem trace_embed (v : EventCodec S B) (t : List S) :
    v.trace (t.map v.embed) = .ok t :=
  Silmaril.Proofs.Containers.Events.trace_embed v t

theorem finite_embed (v : EventCodec S B) (t : List S) (stop : Stop) :
    v.finite (t.map v.embed) stop = .done t stop := by
  simp [finite, trace_embed]

/-- Exact restricted-big/full-small execution relation under actual full-run confinement.
An independent small implementation must additionally refine `restrict M` to inherit specs. -/
theorem expand_restrict (v : EventCodec S B) (M : Model B) (h : M.Sat v.Confined) (b : Beh B) :
    v.expand (v.restrict M) b ↔ M b :=
  Silmaril.Proofs.Containers.Events.expand_restrict v M h b

theorem sat_restrict {v : EventCodec S B} {M : Model B} {N : Model S}
    (simulation : N.Refines (v.restrict M)) {φ : Spec B} (h : M.Sat φ) :
    N.Sat (fun s => φ (s.map v.embed)) := fun s hs => h _ (simulation s hs)

/-- Checking may introduce UB for unsupported events, but never hides source UB. -/
theorem finite_noUB_iff (v : EventCodec S B) (t : List B) (stop : Stop) :
    Spec.noUB (v.finite t stop) ↔
      (∃ ss, v.trace t = .ok ss) ∧ Spec.noUB (.done t stop) :=
  Silmaril.Proofs.Containers.Events.finite_noUB_iff v t stop

end Silmaril.Containers.EventCodec
