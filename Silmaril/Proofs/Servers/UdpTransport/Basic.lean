module

public import Silmaril.Servers.UdpTransport.Defs
public import Silmaril.Servers.Transport.Thms
public import Silmaril.Net.Udp.Network.Thms
public import Mathlib.Data.List.Basic

/-! Proofs for `Silmaril.Servers.UdpTransport.Thms`. -/

@[expose] public section

namespace Silmaril.Servers.Proofs.UdpTransport

open Silmaril.Net.Ip Silmaril.Net.Udp Silmaril.Net.Udp.Network Silmaril.Servers.Transport
open Silmaril.Servers.UdpTransport

variable {a : Endpoint}

/-- The datagrams an item contributes to the flow `i`, given its flow `c`. -/
def units (c i : Conn) : Item → List (List UInt8)
  | .recv bs => if c = i then [bs] else []
  | _ => []

theorem unitsIn_ev (c i : Conn) (it : Item) (r : TTrace Endpoint) :
    unitsIn i (it.ev c :: r) = units c i it ++ unitsIn i r := by
  cases it with
  | recv bs => by_cases h : c = i <;> simp [Item.ev, units, unitsIn, h]
  | send bs => simp [Item.ev, units, unitsIn]
  | err e => simp [Item.ev, units, unitsIn]

theorem unitsIn_open (i : Conn) (p : Transport.Port) (c : Conn) (b : Endpoint) (r : TTrace Endpoint) :
    unitsIn i (TEv.open_ p c b :: r) = unitsIn i r := by simp [unitsIn]

theorem prefix_peersFrom :
    ∀ (t : List Obs) (peers : List Endpoint) (last : Option Endpoint),
      peers <+: peersFrom a peers last t := by
  intro t
  induction t with
  | nil => intro peers _; exact List.prefix_refl _
  | cons o t ih =>
    intro peers last
    simp only [peersFrom]
    split
    · exact ih _ _
    · split
      · exact ih _ _
      · exact (List.prefix_append _ _).trans (ih _ _)

theorem recvFrom_none {last : Option Endpoint} {o : Obs} (h : classify a last o = none)
    (b : Endpoint) (t : List Obs) : recvFrom a b (o :: t) = recvFrom a b t := by
  cases o with
  | recv b' m =>
    by_cases hb : b' = a
    · simp [classify, hb] at h
    · simp [recvFrom, recvAt, hb]
  | send m => rfl
  | sendErr m e => rfl
  | err b' e => rfl

theorem recvFrom_some {c' : Conn} {last : Option Endpoint} {o : Obs} {b' : Endpoint} {it : Item}
    (h : classify a last o = some (b', it)) (b : Endpoint) (c : Conn) (t : List Obs)
    (hc : c = c' ↔ b' = b) :
    recvFrom a b (o :: t) = units c c' it ++ recvFrom a b t := by
  cases o with
  | recv b₀ m =>
    by_cases hb : b₀ = a
    · simp only [classify, hb, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hm : m.src = b
      · have : c = c' := hc.mpr hm
        simp [recvFrom, recvAt, hb, hm, units, this]
      · have : ¬ c = c' := fun h' => hm (hc.mp h')
        simp [recvFrom, recvAt, hb, hm, units, this]
    · simp [classify, hb] at h
  | send m =>
    by_cases hb : m.src = a
    · simp only [classify, hb, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [recvFrom, recvAt, units]
    · simp [classify, hb] at h
  | sendErr m e =>
    by_cases hb : m.src = a
    · simp only [classify, hb, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [recvFrom, recvAt, units]
    · simp [classify, hb] at h
  | err b₀ e =>
    by_cases hb : b₀ = a
    · cases last with
      | none => simp [classify, hb] at h
      | some p =>
        simp only [classify, hb, ↓reduceIte, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [recvFrom, recvAt, units]
    · simp [classify, hb] at h

theorem idxOf_prefix {l P : List Endpoint} (hp : l <+: P) {b : Endpoint} (hb : b ∈ l) :
    P.idxOf b = l.idxOf b := by
  obtain ⟨r, rfl⟩ := hp
  exact List.idxOf_append_of_mem hb

theorem unitsIn_gen :
    ∀ (t : List Obs) (peers : List Endpoint) (last : Option Endpoint) (b : Endpoint),
      b ∈ peersFrom a peers last t →
      unitsIn ((peersFrom a peers last t).idxOf b) (readFrom a peers last t) = recvFrom a b t := by
  intro t
  induction t with
  | nil => intro _ _ _ _; simp [readFrom, unitsIn, recvFrom, recvAt]
  | cons o t ih =>
    intro peers last b hb
    cases hcl : classify a last o with
    | none =>
      simp only [peersFrom, readFrom, hcl] at hb ⊢
      rw [ih _ _ b hb, recvFrom_none hcl]
    | some x =>
      obtain ⟨b', it⟩ := x
      by_cases hin : b' ∈ peers
      · simp only [peersFrom, readFrom, hcl, hin, ↓reduceIte] at hb ⊢
        set P := peersFrom a peers (nextLast a last o) t
        have hpre : peers <+: P := prefix_peersFrom t _ _
        have hb'P : b' ∈ P := hpre.subset hin
        rw [unitsIn_ev, ih _ _ b hb, ← idxOf_prefix hpre hin,
          recvFrom_some hcl b _ t (List.idxOf_inj hb'P)]
      · simp only [peersFrom, readFrom, hcl, hin, ↓reduceIte] at hb ⊢
        set P := peersFrom a (peers ++ [b']) (nextLast a last o) t
        have hpre : peers ++ [b'] <+: P := prefix_peersFrom t _ _
        have hin' : b' ∈ peers ++ [b'] := List.mem_append_right _ (List.mem_singleton_self _)
        have hb'P : b' ∈ P := hpre.subset hin'
        have hlen : P.idxOf b' = peers.length := by
          rw [idxOf_prefix hpre hin', List.idxOf_append_of_notMem hin]
          simp
        rw [unitsIn_open, unitsIn_ev, ih _ _ b hb, ← hlen,
          recvFrom_some hcl b _ t (List.idxOf_inj hb'P)]

theorem unitsIn_flow (t : List Obs) (b : Endpoint) (hb : b ∈ peersFrom a [] none t) :
    unitsIn (flowOf a t b) (read a t) = recvFrom a b t := by
  have := unitsIn_gen t [] none b hb
  simpa [UdpTransport.read, flowOf, unitsIn] using this

/-! ## Port isolation -/

theorem classify_not_atSock {last : Option Endpoint} {o : Obs} (h : Obs.atSock a o = false) :
    classify a last o = none ∧ nextLast a last o = last := by
  cases o with
  | recv b m =>
    have : ¬ b = a := by simpa [Obs.atSock] using h
    simp [classify, nextLast, this]
  | send m =>
    have : ¬ m.src = a := by simpa [Obs.atSock] using h
    simp [classify, nextLast, this]
  | sendErr m e =>
    have : ¬ m.src = a := by simpa [Obs.atSock] using h
    simp [classify, nextLast, this]
  | err b e =>
    have : ¬ b = a := by simpa [Obs.atSock] using h
    simp [classify, nextLast, this]

theorem readFrom_own :
    ∀ (t : List Obs) (peers : List Endpoint) (last : Option Endpoint),
      readFrom a peers last (t.filter (Obs.atSock a)) = readFrom a peers last t := by
  intro t
  induction t with
  | nil => intro _ _; rfl
  | cons o t ih =>
    intro peers last
    cases ho : Obs.atSock a o with
    | false =>
      obtain ⟨hc, hn⟩ := classify_not_atSock (last := last) ho
      rw [List.filter_cons_of_neg (by simp [ho]), ih]
      conv => rhs; unfold readFrom
      rw [hc, hn]
    | true =>
      rw [List.filter_cons_of_pos ho]
      unfold readFrom
      split <;> (try split) <;> rw [ih]

theorem read_own (t : List Obs) : read a (t.filter (Obs.atSock a)) = read a t := by
  simp only [UdpTransport.read, readFrom_own]


/-! ## Authenticity carries over -/

theorem mem_recvAt {m : Msg} : ∀ t : List Obs, m ∈ recvAt a t → Obs.recv a m ∈ t := by
  intro t
  induction t with
  | nil => intro h; cases h
  | cons o t ih =>
    intro h
    cases o with
    | recv b m' =>
      by_cases hb : b = a
      · subst hb
        simp only [recvAt, ↓reduceIte, List.mem_cons] at h
        rcases h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h)
      · simp only [recvAt, hb, ↓reduceIte] at h
        exact List.mem_cons_of_mem _ (ih h)
    | send _ => exact List.mem_cons_of_mem _ (ih h)
    | sendErr _ _ => exact List.mem_cons_of_mem _ (ih h)
    | err _ _ => exact List.mem_cons_of_mem _ (ih h)

theorem received_toChan {m : Msg} {b : Endpoint} :
    ∀ t : List Obs, Obs.recv b m ∈ t → m ∈ Silmaril.Net.Channel.received (toChan t) := by
  intro t
  induction t with
  | nil => intro h; cases h
  | cons o t ih =>
    intro h
    rcases List.mem_cons.mp h with rfl | h
    · simp [toChan, Obs.chan, Silmaril.Net.Channel.received]
    · have := ih h
      cases o with
      | recv _ _ =>
        simp only [toChan, List.filterMap_cons, Obs.chan, Silmaril.Net.Channel.received] at this ⊢
        exact List.mem_cons_of_mem _ this
      | send _ => simpa [toChan, Obs.chan, Silmaril.Net.Channel.received] using this
      | sendErr _ _ => simpa [toChan, List.filterMap_cons, Obs.chan] using this
      | err _ _ => simpa [toChan, List.filterMap_cons, Obs.chan] using this

theorem sent_toChan {m : Msg} : ∀ t : List Obs, m ∈ Silmaril.Net.Channel.sent (toChan t) → Obs.send m ∈ t := by
  intro t
  induction t with
  | nil => intro h; cases h
  | cons o t ih =>
    intro h
    cases o with
    | send m' =>
      simp only [toChan, List.filterMap_cons, Obs.chan, Silmaril.Net.Channel.sent, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)
    | recv _ _ => exact List.mem_cons_of_mem _ (ih h)
    | sendErr _ _ => exact List.mem_cons_of_mem _ (ih h)
    | err _ _ => exact List.mem_cons_of_mem _ (ih h)

theorem flow_authentic {C : Config} (hC : C.offPath = false) {t : List Obs} (ht : t ∈ traces C)
    (b : Endpoint) (hb : b ∈ peersFrom a [] none t) :
    ∀ bs ∈ unitsIn (flowOf a t b) (UdpTransport.read a t),
      ∃ m, Obs.send m ∈ t ∧ m.src = b ∧ m.dst = a ∧ m.data = bs := by
  intro bs hbs
  rw [unitsIn_flow t b hb] at hbs
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hbs
  obtain ⟨hm, hsrc⟩ := List.mem_filter.mp hm
  have hr := mem_recvAt t hm
  have hloc := traces_local ht _ hr
  have hspec := (traces_iff hC t).mp ht
  have hs := Silmaril.Net.Channel.loose_recv_sent hspec.2 m (received_toChan t hr)
  exact ⟨m, sent_toChan t hs, by simpa using hsrc, hloc.1.symm, rfl⟩

end Silmaril.Servers.Proofs.UdpTransport
