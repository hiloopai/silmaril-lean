module

public import Silmaril.Wasi.Versions.Udp.Defs
public import Silmaril.Wasi.Versions.NetMore.Thms
public import Silmaril.Wasi.Versions.Net.Thms

@[expose] public section

/-!
# UDP receive in WASI 0.2 and 0.3: theorems

PROVED (standard axioms):

* **`udpImpl_sat`**: for every inbox `U` and every delivery `D` admitted by `U`
  (`DeliveryOk U D`), the concrete 0.2 host `udpImpl D` is a model of `udpTh U`.
* **`udpImpl3_sat`**: the same for the 0.3 host `udpImpl3 D` and the 0.3 theory `udpTh3 U`.
* `udp3_disjoint`, **`no_udp3_over_p1`**: relation (d) for 0.3 UDP receive (no component
  importing preview1 implements `udpTh3` over preview1 and decides a receive over some
  preview1 host model), with the decisive run `udp3_decisive_example`.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Checks of other functions -/

/-- Functions other than `receive` pass the 0.2 UDP check. -/
theorem udpOk_ne (U : Inbox) (q : UdpSt) {f : FnName} (hf : f ≠ udpReceive) (a : List Val)
    (r : Option (List Val)) : udpOk U q (.imp f a r) = true := by
  unfold udpOk
  split <;> simp_all

/-- Functions other than `receive` pass the 0.3 UDP check. -/
theorem udpOk3_ne (U : Inbox) (q : Udp3St) {f : FnName} (hf : f ≠ udpReceive3) (a : List Val)
    (r : Option (List Val)) : udpOk3 U q (.imp f a r) = true := by
  unfold udpOk3
  split <;> simp_all

/-! ## The 0.2 host -/

/-- A queue prefix of a delivery admitted by `U` passes the receive check. -/
theorem recvOk_take {U : Inbox} {D : Delivery} (hD : DeliveryOk U D) (addr : Val) (n : Nat) :
    recvOk (U addr) (some [okV (some (.record ((D addr).take n)))]) = true := by
  have h : ∀ d ∈ (D addr).take n, U addr d = true := fun d hd =>
    hD addr d (List.mem_of_mem_take hd)
  simpa [recvOk, okV] using h

/-- `receive` of the concrete 0.2 host. -/
theorem udpImpl_receive (D : Delivery) (p : List WEv) (i : BitVec 32) (a : List Val) :
    udpImpl D p udpReceive (.u32 i :: a) =
      (match lookup i (udpState p).ins with
       | some addr => some [okV (some (.record ((D addr).take (maxOf (.u32 i :: a)))))]
       | none => errAnsN eInvalidState) := by
  simp [udpImpl, instanceNetwork, createUdp, udpBind, udpFinishBind, udpStream, udpReceive,
    selfH]; rfl

/-- Every answer of the concrete 0.2 host passes the check. -/
theorem udpImpl_ok {U : Inbox} {D : Delivery} (hD : DeliveryOk U D) (p : List WEv) (f : FnName)
    (a : List Val) : udpOk U (p.foldl udpNext {}) (.imp f a (udpImpl D p f a)) = true := by
  by_cases hf : f = udpReceive
  · subst hf
    rcases a with _ | ⟨v, a'⟩
    · rfl
    cases v
    case u32 i =>
      have hs : p.foldl udpNext {} = udpState p := rfl
      rw [udpImpl_receive, hs]
      cases hl : lookup i (udpState p).ins with
      | none => simp [udpOk, hl]
      | some addr => simpa [udpOk, hl] using recvOk_take hD addr _
    all_goals rfl
  · exact udpOk_ne U _ hf a _

/-- **The concrete 0.2 UDP host of a delivery admitted by `U` is a model of `udpTh U`.** -/
theorem udpImpl_sat {Y : Sig.{0}} {I : Set FnName} {U : Inbox} {D : Delivery}
    (hD : DeliveryOk U D) :
    (hostSat (udpTh U).Accepts).holds (concrete (Y := Y) (I := I) (udpImpl D)) :=
  concrete_sat _ fun _ ht => gated_follows (udpImpl_ok hD) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## The 0.3 host -/

/-- The answer of a queue whose datagrams `U` admits passes the 0.3 receive check. -/
theorem recvOk3_ans {d : Val → Bool} {l : List Val} (h : ∀ x ∈ l, d x = true) :
    recvOk3 d (recvAns3 l) = true := by
  cases l with
  | nil => simp [recvAns3, recvOk3, errV]
  | cons x l => simpa [recvAns3, recvOk3, okV] using h x (List.mem_cons_self ..)

/-- `receive` of the concrete 0.3 host. -/
theorem udpImpl3_receive (D : Delivery) (p : List WEv) (s : BitVec 32) (a : List Val) :
    udpImpl3 D p udpReceive3 (.u32 s :: a) =
      (match lookup s (udpState3 p) with
       | some addr => recvAns3 (D addr)
       | none => recvAns3 []) := by
  simp [udpImpl3, udpCreate3, udpBind3, udpSend3, udpReceive3, selfH]; rfl

/-- Every answer of the concrete 0.3 host passes the check. -/
theorem udpImpl3_ok {U : Inbox} {D : Delivery} (hD : DeliveryOk U D) (p : List WEv) (f : FnName)
    (a : List Val) : udpOk3 U (p.foldl udpNext3 []) (.imp f a (udpImpl3 D p f a)) = true := by
  by_cases hf : f = udpReceive3
  · subst hf
    rcases a with _ | ⟨v, a'⟩
    · rfl
    cases v
    case u32 s =>
      have hs : p.foldl udpNext3 [] = udpState3 p := rfl
      rw [udpImpl3_receive, hs]
      cases hl : lookup s (udpState3 p) with
      | none => simp [udpOk3, hl]
      | some addr => simpa [udpOk3, hl] using recvOk3_ans (hD addr)
    all_goals rfl
  · exact udpOk3_ne U _ hf a _

/-- **The concrete 0.3 UDP host of a delivery admitted by `U` is a model of `udpTh3 U`.** -/
theorem udpImpl3_sat {Y : Sig.{0}} {I : Set FnName} {U : Inbox} {D : Delivery}
    (hD : DeliveryOk U D) :
    (hostSat (udpTh3 U).Accepts).holds (concrete (Y := Y) (I := I) (udpImpl3 D)) :=
  concrete_sat _ fun _ ht => gated_follows (udpImpl3_ok hD) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## Relation (d) for 0.3 UDP -/

/-- Every inbox and the quiet one admit no common decisive 0.3 answer. -/
theorem udp3_disjoint (U : Inbox) (q : Udp3St) (e : WEv) (hd : udpDecisive3 q e)
    (_ : udpOk3 U q e = true) : udpOk3 udpQuiet q e = false := by
  obtain ⟨s, a, x, rfl, hs⟩ := hd
  obtain ⟨addr, hl⟩ := Option.isSome_iff_exists.1 hs
  simp [udpOk3, hl, recvOk3, udpQuiet]

/-- **0.3 UDP receive is not implementable over preview1.** -/
theorem no_udp3_over_p1 {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ (ObsOverP1 [] udpNext3 udpOk3 σ ∧ ObsResponsive [] udpNext3 udpDecisive3 σ) :=
  no_obs_over_p1 (fun _ _ => true) udpQuiet (udp3_disjoint _) σ

/-- A 0.3 run: bind socket `3`, then receive one datagram. -/
def udp3Run : List WEv :=
  [.imp udpBind3 [.u32 3, addr0] (some [.variant 0 none]),
   .imp udpReceive3 [.u32 3] (some [.variant 0 (some (.record [.record [], addr0]))])]

/-- The hypotheses of `no_udp3_over_p1` are satisfiable: a decisive run of a 0.3 theory. -/
theorem udp3_decisive_example :
    (udpTh3 fun _ _ => true).Accepts udp3Run ∧ Decides [] udpNext3 udpDecisive3 udp3Run := by
  refine ⟨by unfold Protocol.Accepts; decide,
    [.imp udpBind3 [.u32 3, addr0] (some [.variant 0 none])], _, [], rfl, 3, [], _, rfl, ?_⟩
  decide

end Silmaril.Wasi.Versions.Net
