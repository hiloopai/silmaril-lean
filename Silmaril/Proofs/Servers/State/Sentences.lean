module

public import Silmaril.Servers.State.Sentences.Defs
public import Silmaril.Servers.State.Traces.Defs

/-!
# Proofs: reading statements about histories as core sentences

The events of the core trace of a history are its events, each request `i` at the identity
`⟨i, 0⟩` (`mem_toTrace_recv`, `mem_toTrace_send`), so statements about the calls and returns
of every history of a server are core atomic sentences of its model (`model_sat_atomic`), and
distinct answers to distinct identities are `Sen.distinct` (`model_sat_distinct`).
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.State.Sentences

open Silmaril.Servers Silmaril.Servers.State

variable {Req Resp : Type}

theorem mem_toTrace_recv {H : Hist Req Resp} {j : ReqId} {r : Req} :
    Event.recv (A := sig Req Resp) j r ∈ toTrace H ↔ j.seq = 0 ∧ Ev.call j.conn r ∈ H := by
  simp only [toTrace, List.mem_map]
  constructor
  · rintro ⟨e, he, hee⟩
    cases e with
    | call i r' =>
      simp only [Ev.toEvent, Event.recv.injEq] at hee
      obtain ⟨rfl, rfl⟩ := hee
      exact ⟨rfl, he⟩
    | ret i s => simp [Ev.toEvent] at hee
  · rintro ⟨h0, hc⟩
    obtain ⟨c, k⟩ := j
    simp only at h0 hc
    subst h0
    exact ⟨_, hc, rfl⟩

theorem mem_toTrace_send {H : Hist Req Resp} {j : ReqId} {s : Resp} :
    Event.send (A := sig Req Resp) j s ∈ toTrace H ↔ j.seq = 0 ∧ Ev.ret j.conn s ∈ H := by
  simp only [toTrace, List.mem_map]
  constructor
  · rintro ⟨e, he, hee⟩
    cases e with
    | ret i s' =>
      simp only [Ev.toEvent, Event.send.injEq] at hee
      obtain ⟨rfl, rfl⟩ := hee
      exact ⟨rfl, he⟩
    | call i r => simp [Ev.toEvent] at hee
  · rintro ⟨h0, hc⟩
    obtain ⟨c, k⟩ := j
    simp only at h0 hc
    subst h0
    exact ⟨_, hc, rfl⟩

theorem model_sat_atomic {M : Server Req Resp} {R : Req → Resp → Prop}
    (h : ∀ H, M.Hists H → ∀ i r s, Ev.call i r ∈ H → Ev.ret i s ∈ H → R r s) :
    M.model.Sat (Sen.atomic R) := by
  rintro t ⟨H, hH, rfl⟩ j r s hr hs
  exact h H hH j.conn r s (mem_toTrace_recv.1 hr).2 (mem_toTrace_send.1 hs).2

theorem model_sat_distinct {M : Server Req Resp}
    (h : ∀ H, M.Hists H → ∀ i j a b, Ev.ret i a ∈ H → Ev.ret j b ∈ H → i ≠ j → a ≠ b) :
    M.model.Sat Sen.distinct := by
  rintro t ⟨H, hH, rfl⟩ j k a b hj hk hjk
  obtain ⟨hj0, hj'⟩ := mem_toTrace_send.1 hj
  obtain ⟨hk0, hk'⟩ := mem_toTrace_send.1 hk
  refine h H hH j.conn k.conn a b hj' hk' fun hc => hjk ?_
  obtain ⟨c, x⟩ := j
  obtain ⟨c', y⟩ := k
  simp only at hj0 hk0 hc
  subst hj0 hk0 hc
  rfl

end Silmaril.Proofs.Servers.State.Sentences
