module

public import Silmaril.Net.Udp.QuicCarrier.Defs
public import Silmaril.Net.Http3.Datagram.Thms
public import Batteries.Data.List.Perm

/-! Proofs for `Silmaril.Net.Udp.QuicCarrier.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Udp.Proofs.QuicCarrier

open Silmaril.Net.Quic Silmaril.Net.Quic.Service Silmaril.Net.Udp.Network
open Silmaril.Net.Udp.QuicCarrier List

/-- The carrier invariant, relating the carrier's state to the abstract connection. -/
structure Inv (s : St) (c : Conn) : Prop where
  dg : c.datagrams = true
  sent : c.dgSent .client = s.sent.map Pkt.payload
  recv : c.dgRecv .server = s.accepted.map Pkt.payload
  accNodup : s.accepted.Nodup
  accSub : ∀ p ∈ s.accepted, p ∈ s.sent
  sentNodup : s.sent.Nodup
  pnLt : ∀ p ∈ s.sent, p.pn < s.next
  seen : s.seen = s.accepted.map Pkt.pn

theorem Inv.subperm {s : St} {c : Conn} (h : Inv s c) : s.accepted <+~ s.sent :=
  List.subperm_of_subset h.accNodup h.accSub

theorem subperm_filterMap {α β : Type} (f : α → Option β) {l₁ l₂ : List α} (h : l₁ <+~ l₂) :
    l₁.filterMap f <+~ l₂.filterMap f := by
  obtain ⟨l, hp, hs⟩ := h
  exact ⟨l.filterMap f, hp.filterMap f, hs.filterMap f⟩

theorem subperm_map {α β : Type} (f : α → β) {l₁ l₂ : List α} (h : l₁ <+~ l₂) :
    l₁.map f <+~ l₂.map f := by
  obtain ⟨l, hp, hs⟩ := h
  exact ⟨l.map f, hp.map f, hs.map f⟩

theorem inv_init (limit : StreamType → Nat) : Inv {} (conn0 limit) where
  dg := rfl
  sent := rfl
  recv := rfl
  accNodup := List.nodup_nil
  accSub := by simp
  sentNodup := List.nodup_nil
  pnLt := by simp
  seen := rfl

theorem accept?_some {P : Protection} {k : P.Key} {s : St} {c : List UInt8} {p : Pkt}
    (h : s.accept? P k c = some p) : P.unprotect k c = some p ∧ p.pn ∉ s.seen := by
  unfold St.accept? at h
  split at h
  · rename_i p' hp'
    split at h
    · cases h
    · rename_i hn
      cases h
      exact ⟨hp', hn⟩
  · cases h

theorem inv_send {s : St} {c : Conn} (h : Inv s c) (d : List UInt8) :
    Inv (s.send d) { c with dgSent := upd c.dgSent .client (c.dgSent .client ++ [d]) } where
  dg := h.dg
  sent := by simp [upd, St.send, h.sent]
  recv := h.recv
  accNodup := h.accNodup
  accSub := fun p hp => List.mem_append_left _ (h.accSub p hp)
  sentNodup := by
    refine List.nodup_append.mpr ⟨h.sentNodup, (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩), ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton.mp hb] at hab
    subst hab
    exact Nat.lt_irrefl _ (h.pnLt _ ha)
  pnLt := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact Nat.lt_succ_of_lt (h.pnLt p hp)
    · rw [List.mem_singleton.mp hp]; exact Nat.lt_succ_self _
  seen := h.seen

theorem inv_deliver {s : St} {c : Conn} (h : Inv s c) {p : Pkt} (hp : p ∈ s.sent)
    (hn : p.pn ∉ s.seen) :
    Inv (s.deliver p) { c with dgRecv := upd c.dgRecv .server (c.dgRecv .server ++ [p.payload]) } where
  dg := h.dg
  sent := h.sent
  recv := by simp [upd, St.deliver, h.recv]
  accNodup := by
    refine List.nodup_append.mpr ⟨h.accNodup, (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩), ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton.mp hb] at hab
    subst hab
    exact hn (h.seen ▸ List.mem_map_of_mem ha)
  accSub := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact h.accSub q hq
    · rw [List.mem_singleton.mp hq]; exact hp
  sentNodup := h.sentNodup
  pnLt := h.pnLt
  seen := by simp [St.deliver, h.seen]

theorem carrier_sound_gen (P : Protection) (k : P.Key) :
    ∀ (es : List Ev) (s : St) (c : Conn), Inv s c → Hon P k s es →
      ∃ c', ConnSteps c (appTrace P k s es) c' ∧ Inv (s.run P k es) c' := by
  intro es
  induction es with
  | nil => intro s c h _; exact ⟨c, .refl c, h⟩
  | cons e es ih =>
    intro s c h hh
    cases e with
    | appSend d =>
      obtain ⟨c', hs, hi⟩ := ih (s.send d) _ (inv_send h d) hh
      exact ⟨c', .cons (.sendDatagram .client d h.dg) hs, hi⟩
    | udpRecv m =>
      obtain ⟨hopen, hh'⟩ := hh
      cases ha : s.accept? P k m.data with
      | none =>
        have hst : s.step P k (.udpRecv m) = s := by simp [St.step, ha]
        rw [hst] at hh'
        obtain ⟨c', hs, hi⟩ := ih s c h hh'
        refine ⟨c', ?_, ?_⟩
        · simpa [appTrace, ha] using hs
        · show Inv ((es.foldl (St.step P k) (s.step P k (.udpRecv m)))) c'
          rw [hst]; exact hi
      | some p =>
        obtain ⟨hu, hn⟩ := accept?_some ha
        have hp : p ∈ s.sent := hopen p hu
        have hst : s.step P k (.udpRecv m) = s.deliver p := by simp [St.step, ha]
        rw [hst] at hh'
        have hi1 := inv_deliver h hp hn
        obtain ⟨c', hs, hi⟩ := ih (s.deliver p) _ hi1 hh'
        have hcount : (c.dgRecv .server ++ [p.payload]).count p.payload ≤
            (c.dgSent (Role.peer .server)).count p.payload := by
          have hsub := hi1.subperm
          have hm := (subperm_map Pkt.payload hsub).count_le p.payload
          simp only [St.deliver, List.map_append, List.map_cons, List.map_nil] at hm
          rw [h.recv]
          show _ ≤ (c.dgSent .client).count p.payload
          rw [h.sent]
          simpa [St.deliver] using hm
        refine ⟨c', ?_, ?_⟩
        · simp only [appTrace, ha]
          exact .cons (.recvDatagram .server p.payload hcount) hs
        · show Inv ((es.foldl (St.step P k) (s.step P k (.udpRecv m)))) c'
          rw [hst]; exact hi

theorem carrier_sound (P : Protection) (k : P.Key) (limit : StreamType → Nat) (es : List Ev)
    (h : Hon P k {} es) : ∃ c', ConnSteps (conn0 limit) (appTrace P k {} es) c' := by
  obtain ⟨c', hs, _⟩ := carrier_sound_gen P k es {} (conn0 limit) (inv_init limit) h
  exact ⟨c', hs⟩

theorem accepted_subperm (P : Protection) (k : P.Key) (es : List Ev) (h : Hon P k {} es) :
    (St.run P k {} es).accepted.map Pkt.payload <+~ (St.run P k {} es).sent.map Pkt.payload := by
  obtain ⟨_, _, hi⟩ := carrier_sound_gen P k es {} (conn0 (fun _ => 0)) (inv_init _) h
  exact subperm_map _ hi.subperm

theorem run_sent (P : Protection) (k : P.Key) :
    ∀ (es : List Ev) (s : St),
      (St.run P k s es).sent.map Pkt.payload = s.sent.map Pkt.payload ++ sentPayloads es := by
  intro es
  induction es with
  | nil => intro s; simp [St.run, sentPayloads]
  | cons e es ih =>
    intro s
    cases e with
    | appSend d =>
      show (St.run P k (s.send d) es).sent.map Pkt.payload = _
      rw [ih]; simp [St.send, sentPayloads]
    | udpRecv m =>
      show (St.run P k (s.step P k (.udpRecv m)) es).sent.map Pkt.payload = _
      rw [ih]
      cases ha : s.accept? P k m.data <;> simp [St.step, ha, St.deliver, sentPayloads]

theorem hon_of_replay (P : Protection) (k : P.Key) (hP : P.Correct) :
    ∀ (es : List Ev) (s : St), Replay P k s es → Hon P k s es := by
  intro es
  induction es with
  | nil => intro _ _; trivial
  | cons e es ih =>
    intro s h
    cases e with
    | appSend d => exact ih (s.send d) h
    | udpRecv m =>
      obtain ⟨⟨p, hp, hm⟩, h'⟩ := h
      refine ⟨fun q hq => ?_, ih _ h'⟩
      rw [hm, hP k p] at hq
      cases hq
      exact hp

theorem h3Decode_encode (hs : List Http3.Datagram) (hv : ∀ h ∈ hs, h.Valid) :
    h3Decode (hs.map Http3.Datagram.encode) = hs := by
  induction hs with
  | nil => rfl
  | cons h t ih =>
    have h1 := Http3.Datagram.decode_encode (hv h List.mem_cons_self)
    have h2 := ih fun x hx => hv x (List.mem_cons_of_mem _ hx)
    simp only [h3Decode, List.map_cons, List.filterMap_cons, h1, Except.toOption] at h2 ⊢
    rw [h2]

theorem h3_received_subperm (P : Protection) (k : P.Key) (es : List Ev) (h : Hon P k {} es)
    (hs : List Http3.Datagram) (hv : ∀ x ∈ hs, x.Valid)
    (hsent : sentPayloads es = hs.map Http3.Datagram.encode) :
    h3Decode ((St.run P k {} es).accepted.map Pkt.payload) <+~ hs := by
  have h1 := subperm_filterMap (fun d => (Http3.Datagram.decode d).toOption)
    (accepted_subperm P k es h)
  have h2 := run_sent P k es {}
  simp only [List.map_nil, List.nil_append] at h2
  rw [h2, hsent] at h1
  have h3 := h3Decode_encode hs hv
  unfold h3Decode at h3 ⊢
  rw [h3] at h1
  exact h1

/-! ## Forgery without protection -/

theorem none_forgery (limit : StreamType → Nat) (cli srv : Endpoint) :
    appTrace Protection.none () {} [.udpRecv (Msg.mk' cli srv [0, 0x61])] =
        [.recvDatagram .server [0x61]] ∧
      ¬ ∃ c', ConnSteps (conn0 limit) [.recvDatagram .server [0x61]] c' := by
  refine ⟨rfl, ?_⟩
  rintro ⟨c', hs⟩
  cases hs with
  | cons hstep _ =>
    cases hstep with
    | recvDatagram _ _ hc =>
      simp [conn0, Conn.initial, Role.peer] at hc

end Silmaril.Net.Udp.Proofs.QuicCarrier
