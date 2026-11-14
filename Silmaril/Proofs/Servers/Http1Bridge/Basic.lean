module

public import Silmaril.Servers.Http1Bridge.Defs
public import Silmaril.Servers.Core.Thms

/-!
# Proofs: the exchange reading of the HTTP/1.1 institution

A response obligation holds of a model iff its relation holds of every exchange the
implementation allows; the server of an implementation satisfies an atomic sentence iff the
relation holds of every allowed exchange (each exchange is a one-request trace of the server).
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Http1Bridge

open Silmaril.Servers Silmaril.Servers.Http1Bridge
open Silmaril.Net.Http1 Silmaril.Net.Http1.Inst

theorem sat_iff_forall {A : Inst.Sig} (M : Inst.Model A) :
    ∀ (φ : Inst.Sen A) {R}, respRel M φ = some R →
      (Inst.Sat M φ ↔ ∀ q p, exch M.impl q p → R q p)
  | .status m r cs, R, h => by
    cases h
    exact ⟨fun H q p hx hv hm hr => H q.1 q.2 p.1 p.2 hv hm hr hx,
      fun H h b rh rb hv hm hr hx => H (h, b) (rh, rb) hx hv hm hr⟩
  | .notStatus m r cs, R, h => by
    cases h
    exact ⟨fun H q p hx hv hm hr => H q.1 q.2 p.1 p.2 hv hm hr hx,
      fun H h b rh rb hv hm hr hx => H (h, b) (rh, rb) hx hv hm hr⟩
  | .respField m r f, R, h => by
    cases h
    exact ⟨fun H q p hx hv hm hr => H q.1 q.2 p.1 p.2 hv hm hr hx,
      fun H h b rh rb hv hm hr hx => H (h, b) (rh, rb) hx hv hm hr⟩
  | .noRespField f, R, h => by
    cases h
    exact ⟨fun H q p hx => H q.1 q.2 p.1 p.2 hx, fun H h b rh rb hx => H (h, b) (rh, rb) hx⟩
  | .unknownMethods ks cs, R, h => by
    cases h
    exact ⟨fun H q p hx hv hm => H q.1 q.2 p.1 p.2 hv hm hx,
      fun H h b rh rb hv hm hx => H (h, b) (rh, rb) hx hv hm⟩
  | .headNoContent, R, h => by
    cases h
    exact ⟨fun H q p hx hm => H q.1 q.2 p.1 p.2 hm hx, fun H h b rh rb hm hx => H (h, b) (rh, rb) hx hm⟩
  | .wellFramed, R, h => by
    cases h
    exact ⟨fun H q p hx => H q.1 q.2 p.1 p.2 hx, fun H h b rh rb hx => H (h, b) (rh, rb) hx⟩
  | .conj φ ψ, R, h => by
    simp only [respRel] at h
    cases hφ : respRel M φ with
    | none => rw [hφ] at h; cases h
    | some R₁ =>
      cases hψ : respRel M ψ with
      | none => rw [hφ, hψ] at h; cases h
      | some R₂ =>
        rw [hφ, hψ] at h
        cases h
        rw [show Inst.Sat M (.conj φ ψ) = (Inst.Sat M φ ∧ Inst.Sat M ψ) from rfl,
          sat_iff_forall M φ hφ, sat_iff_forall M ψ hψ]
        exact ⟨fun ⟨h1, h2⟩ q p hx => ⟨h1 q p hx, h2 q p hx⟩,
          fun H => ⟨fun q p hx => (H q p hx).1, fun q p hx => (H q p hx).2⟩⟩
  | .implements _, _, h => by cases h
  | .framesSafely, _, h => by cases h
  | .closesOnClTe, _, h => by cases h
  | .neg _, _, h => by cases h

theorem server_sat_iff (I : Impl) (R : RequestHead × Body → ResponseHead × Body → Prop) :
    (implServer I).Sat (Sen.atomic (A := wireSig) R) ↔ ∀ q p, exch I q p → R q p := by
  constructor
  · intro H q p hx
    have hm : (implServer I).Tr (Trace.seq (A := wireSig) [(⟨0, 0⟩, q, p)]) := by
      rw [implServer, Machine.server_tr_iff, Sen.lin_seq_iff _ (by simp)]
      exact ⟨(), .cons hx (.nil _)⟩
    exact H _ hm ⟨0, 0⟩ q p (by simp [Trace.seq]) (by simp [Trace.seq])
  · intro H t ht
    exact Sen.atomic_mono (fun q p hx => H q p hx) t
      ((Machine.server_ofRel_tr_iff (A := wireSig) (exch I) t).1 ht).2

end Silmaril.Proofs.Servers.Http1Bridge
