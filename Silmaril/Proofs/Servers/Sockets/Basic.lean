module

public import Silmaril.Servers.Sockets.Defs

/-!
# Socket events of a Linux process: proofs

For `Silmaril.Servers.Sockets.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Sockets

open Silmaril.Process Silmaril.Servers.Platform Silmaril.Servers.Sockets

theorem received_append (c : ConnId) : ∀ a b : List SockEv,
    received c (a ++ b) = received c a ++ received c b
  | [], _ => rfl
  | e :: a, b => by
    cases e <;> simp [received, received_append c a b]

theorem sent_append (c : ConnId) : ∀ a b : List SockEv,
    sent c (a ++ b) = sent c a ++ sent c b
  | [], _ => rfl
  | e :: a, b => by
    cases e <;> simp [sent, sent_append c a b]

theorem ofEvents_cons (e : LPS.Event) (evs : List LPS.Event) :
    ofEvents (e :: evs) = ofEvent e ++ ofEvents evs := List.flatMap_cons

theorem received_ofEvents (c : ConnId) : ∀ evs : List LPS.Event,
    received c (ofEvents evs) = recvBytes c evs
  | [] => rfl
  | e :: evs => by
    rw [ofEvents_cons, received_append, received_ofEvents c evs]
    simp only [recvBytes, List.flatMap_cons]
    congr 1
    cases e with
    | readEv ch b => cases h : connOf ch <;> simp [ofEvent, h, received]
    | writeEv ch b => cases h : connOf ch <;> simp [ofEvent, h, received]
    | exitEv => rfl
    | killEv => rfl

theorem sent_ofEvents (c : ConnId) : ∀ evs : List LPS.Event,
    sent c (ofEvents evs) = sentBytes c evs
  | [] => rfl
  | e :: evs => by
    rw [ofEvents_cons, sent_append, sent_ofEvents c evs]
    simp only [sentBytes, List.flatMap_cons]
    congr 1
    cases e with
    | readEv ch b => cases h : connOf ch <;> simp [ofEvent, h, sent]
    | writeEv ch b => cases h : connOf ch <;> simp [ofEvent, h, sent]
    | exitEv => rfl
    | killEv => rfl

theorem ofEvents_byteTrace (r : LPS.StepRecord) (rs : List LPS.StepRecord) :
    ofEvents (LPS.byteTrace (r :: rs)) = ofEvents r.events ++ ofEvents (LPS.byteTrace rs) := by
  simp only [ofEvents, LPS.byteTrace, List.flatMap_cons, List.flatMap_append]

theorem received_ofRecords (isAccept : LPS.Word → Bool) (c : ConnId) :
    ∀ (n : Nat) (h : List LPS.StepRecord),
      received c (ofRecords isAccept n h) = received c (ofEvents (LPS.byteTrace h))
  | _, [] => rfl
  | n, r :: rs => by
    rw [ofEvents_byteTrace, received_append]
    cases ha : accepts isAccept r
    · simp only [ofRecords, ha, Bool.false_eq_true, ↓reduceIte, received_append,
        received_ofRecords isAccept c n rs]
    · simp only [ofRecords, ha, ↓reduceIte]
      show received c (ofEvents r.events ++ ofRecords isAccept (n + 1) rs) = _
      rw [received_append, received_ofRecords isAccept c (n + 1) rs]

theorem sent_ofRecords (isAccept : LPS.Word → Bool) (c : ConnId) :
    ∀ (n : Nat) (h : List LPS.StepRecord),
      sent c (ofRecords isAccept n h) = sent c (ofEvents (LPS.byteTrace h))
  | _, [] => rfl
  | n, r :: rs => by
    rw [ofEvents_byteTrace, sent_append]
    cases ha : accepts isAccept r
    · simp only [ofRecords, ha, Bool.false_eq_true, ↓reduceIte, sent_append,
        sent_ofRecords isAccept c n rs]
    · simp only [ofRecords, ha, ↓reduceIte]
      show sent c (ofEvents r.events ++ ofRecords isAccept (n + 1) rs) = _
      rw [sent_append, sent_ofRecords isAccept c (n + 1) rs]

end Silmaril.Proofs.Servers.Sockets
