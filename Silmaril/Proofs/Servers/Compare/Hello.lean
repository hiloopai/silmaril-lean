module

public import Silmaril.Servers.Compare.Defs
public import Silmaril.Servers.Wire1.Thms
public import Silmaril.Servers.WasiExamples.Thms
public import Silmaril.Servers.Platform.Thms

/-!
# Comparing a `wasi:http` component with a Linux process: proofs

For `Silmaril.Servers.Compare.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Compare

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Servers.Platform Silmaril.Servers.Wire1 Silmaril.Servers.Reuse
open Silmaril.Servers.Compare
open Silmaril.Net.Http (Request Response)
open Silmaril.Net.Http1 (methodHEAD methodCONNECT)
open Silmaril.Cli (Input Interleave)

theorem interleave_mem {α : Type} {a b l : List α} (h : Interleave a b l) {x : α} (hx : x ∈ l) :
    x ∈ a ∨ x ∈ b := by
  induction h with
  | nil => simp at hx
  | left _ ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact .inl List.mem_cons_self
    · exact (ih hx).imp (List.mem_cons_of_mem _) id
  | right _ ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact .inr List.mem_cons_self
    · exact (ih hx).imp id (List.mem_cons_of_mem _)

theorem merge_mem {ls : List Log} {l : Log} (h : Merge ls l) {x : Request × Response}
    (hx : x ∈ l) : ∃ m ∈ ls, x ∈ m := by
  induction h with
  | nil => simp at hx
  | cons _ hi ih =>
    rcases interleave_mem hi hx with hx | hx
    · exact ⟨_, List.mem_cons_self, hx⟩
    · obtain ⟨m, hm, hxm⟩ := ih hx
      exact ⟨m, List.mem_cons_of_mem _ hm, hxm⟩

theorem toResponse_helloWire : toResponse helloWire = helloResp := by decide

theorem helloWire_ok {meth : List UInt8} (h1 : meth ≠ methodHEAD) (h2 : meth ≠ methodCONNECT) :
    RespOk meth helloWire := by
  refine ⟨by decide, ?_⟩
  have hb : Net.Http1.bodyLengthOfFields helloFields .close .close = .length 5 := by decide
  have hr : Net.Http1.responseBodyLength meth 200 helloFields = .length 5 := by
    have c1 : ¬(meth = methodHEAD ∨ 200 / 100 = 1 ∨ 200 = 204 ∨ 200 = 304) := by simp [h1]
    simp only [Net.Http1.responseBodyLength, c1, ↓reduceIte, hb, h2, and_true]
  show Net.Http1.Body.Fits (Net.Http1.responseBodyLength meth 200 helloFields)
    (.content helloResp.content)
  rw [hr]
  exact (by decide : helloResp.content.length = 5)

theorem wasi_hello_iff (l : Log) : wasi.view hello l ↔ ∀ p ∈ l, p.2 = helloResp := by
  constructor
  · rintro ⟨o, ho, rfl⟩ p hp
    exact hello_sat _ (ho p hp) p List.mem_cons_self
  · intro h
    refine ⟨l, fun p hp => ?_, rfl⟩
    obtain ⟨q, r⟩ := p
    have : r = helloResp := h _ hp
    subst this
    exact hello_answers q

theorem wire_choose : ∀ l : Log, wireLog l → ∃ ms : List WireReq,
    (∀ m ∈ ms, WireOk m) ∧ ms.map toRequest = l.map Prod.fst
  | [], _ => ⟨[], by simp, rfl⟩
  | p :: l, h => by
    obtain ⟨m, hm1, hm4⟩ := h p List.mem_cons_self
    obtain ⟨ms, hms, he⟩ := wire_choose l fun q hq => h q (List.mem_cons_of_mem _ hq)
    refine ⟨m :: ms, fun x hx => ?_, by simp [hm4, he]⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hm1
    · exact hms x hx

theorem forall₂_hello : ∀ ms : List WireReq, (∀ m ∈ ms, WireOk m) →
    List.Forall₂ (fun r m => RespOk r.method.toToken m) (ms.map toRequest)
      (ms.map fun _ => helloWire)
  | [], _ => .nil
  | m :: ms, h => by
    simp only [List.map_cons]
    refine .cons ?_ (forall₂_hello ms fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [method_toRequest]
    exact helloWire_ok (h m List.mem_cons_self).2.1 (h m List.mem_cons_self).2.2

theorem zip_hello : ∀ (l : Log) (ms : List WireReq), ms.map toRequest = l.map Prod.fst →
    (∀ p ∈ l, p.2 = helloResp) →
    (ms.map toRequest).zip ((ms.map fun _ => helloWire).map toResponse) = l
  | [], [], _, _ => rfl
  | [], _ :: _, he, _ => by simp at he
  | _ :: _, [], he, _ => by simp at he
  | (q, r) :: l, m :: ms, he, hp => by
    simp only [List.map_cons, List.cons.injEq] at he
    have hr : r = helloResp := hp (q, r) List.mem_cons_self
    subst hr
    have ih := zip_hello l ms he.2 fun p hp' => hp p (List.mem_cons_of_mem _ hp')
    simp only [List.map_cons, List.zip_cons_cons, toResponse_helloWire, he.1, ih]

theorem wasi_refines_linux {L : SockSem} {inp : Input} (hL : ServesHello L inp) :
    Refines (restrict wasi wireLog) linux1 hello (L, inp) := by
  rintro l ⟨o, ho, rfl, hw⟩
  have hall := (wasi_hello_iff o).1 ⟨o, ho, rfl⟩
  obtain ⟨ms, hms, he⟩ := wire_choose o hw
  obtain ⟨tr, htr, hacc, hrec, hsent⟩ := hL ms hms
  have hc := connLog_encode hrec hsent (fun m hm => (hms m hm).1) (forall₂_hello ms hms)
  refine ⟨tr, htr, (accepted tr, connLog framing tr), rfl, ?_⟩
  show Merge ((accepted tr).map (connLog framing tr)) o
  rw [hacc, List.map_cons, List.map_nil, hc, zip_hello o ms he hall]
  exact merge_single o

theorem linux_refines_wasi {L : SockSem} {inp : Input} (hL : OnlyHello L inp) :
    Refines linux1 wasi (L, inp) hello := by
  rintro l ⟨tr, htr, t, rfl, hm⟩
  refine (wasi_hello_iff l).2 fun p hp => ?_
  obtain ⟨x, hx, hpx⟩ := merge_mem hm hp
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  exact hL tr htr c p hpx

theorem connLog_nil {tr : List SockEv} {c : ConnId} (h : received c tr = []) :
    connLog framing tr c = [] := by
  show (requests (received c tr)).zip _ = []
  rw [h]
  rfl

theorem helloSock_serves (inp : Input) : ServesHello helloSock inp := fun ms hms =>
  ⟨_, ⟨ms, hms, rfl⟩, rfl, by simp [received], by simp [sent]⟩

theorem helloSock_only (inp : Input) : OnlyHello helloSock inp := by
  rintro tr ⟨ms, hms, rfl⟩ c p hp
  by_cases hc : c = 0
  · subst hc
    rw [connLog_encode (by simp [received]) (by simp [sent]) (fun m hm => (hms m hm).1)
      (forall₂_hello ms hms)] at hp
    obtain ⟨x, hx, e⟩ := List.mem_map.1 (List.of_mem_zip hp).2
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
    rw [← e]
    exact toResponse_helloWire
  · rw [connLog_nil (by simp [received, Ne.symm hc])] at hp
    simp at hp

end Silmaril.Proofs.Servers.Compare
