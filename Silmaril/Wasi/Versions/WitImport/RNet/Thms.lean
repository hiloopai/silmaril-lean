module

public import Silmaril.Wasi.Versions.WitImport.RNetTyping.Thms
public import Silmaril.Wasi.Versions.WitImport.RP3.Thms
public import Silmaril.Wasi.Versions.WitImport.Http3.Thms
public import Silmaril.Wasi.Versions.Net3.Defs
public import Silmaril.Wasi.Versions.Http3.Defs

/-!
# TCP and HTTP against the resolved WIT typing

An earlier step of Follow-up 3 (`Silmaril.Wasi.Versions.WitImport.NetTyping`, `…Http3`) compared the TCP
and HTTP theories with the unresolved typing, where every `error-code` is unconstrained. With
the named types resolved (`sock2P`, `sock3P`, `http2P`, `http3P`):

* 0.2 `wasi:sockets/network.error-code` is an enum of 21 cases (`tcpErr_eq`); 0.3
  `wasi:sockets/types.error-code` a variant of 15 cases whose last, `other`, carries an
  `option<string>`; the HTTP `error-code` a variant of 39 cases, 15 of them with payloads.

The results:

* **0.2 TCP** (`tcpOk_witR`): on a pending socket, an accepted `finish-connect` answer is
  resolved-typed **when the network's codes are codes** (`TypedNet N 21`). **REFUTED**
  without that condition (`tcpOk_not_witR_code`: a network failing with code 21).
* **0.3 TCP**: **REFUTED** sound direction (`tcpOk3_not_witR`): `Net.connectOk3` checks only
  the case number of the error, so it accepts `error(access-denied(true))`. **Restated**:
  the theory's canonical answers are typed (`outcomeAns3_witR`: `Net.outcomeAns3 o` for a
  code `< 15`, `other` with its `none`), so the concrete host `Net.tcpImpl3 N3` answers with
  the resolved types for a typed network (`tcpImpl3_witR`).
* **0.2 HTTP** (`httpOk_witR_up`): on a future of a request, for a web that never fails, an
  accepted `get` answer is resolved-typed. **REFUTED** for a failing web
  (`httpOk_not_witR`: the error payload is unchecked).
* **0.3 HTTP** (`http3Ok_witR_up`): for a web that never fails, an accepted `send` answer is
  resolved-typed or a trap. **REFUTED** for a failing web (`http3Ok_not_witR`).
* **The concrete HTTP hosts answer ill-typed errors** (`httpAns_not_witR`): both hosts answer
  a failure `k` with `error-code` case `k` *without* payload, and case `14`
  (`TLS-alert-received`) has a payload. For payload-free codes the answer is typed
  (`httpAns_witR`, `sendAns_witR`, e.g. `DNS-timeout` of `webDown`).
* **Converses REFUTED with resolved-typed answers and arguments**
  (`finish_witR_not_tcpOk`, `connect_witR_not_tcpTh3`, `send_witR_not_http3`): the theories
  pin the outcome to the network, the WIT type does not.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasi.Versions

/-- Every failure of the network `N` is a code below `m`. -/
def TypedNet (N : Net.Network) (m : Nat) : Prop := ∀ a k, N a = some k → k < m

/-- A web that never fails. -/
def WebUp (W : Net.Web) : Prop := ∀ a p, ∃ s, W a p = .status s

theorem kindOk_type {ok : Binary.IfaceName → Binary.Ty → Val → Bool} {j : Binary.IfaceName}
    {t : Binary.Ty} (v : Val) : kindOk ok j (.type t) v = ok j t v := by
  cases v <;> rfl

/-! ## Signatures and error codes -/

/-- `wasi:sockets/tcp@0.2.12`. -/
abbrev tcpI : Binary.IfaceName := iface2 "sockets" "tcp"
/-- `wasi:sockets/network@0.2.12`. -/
abbrev netI : Binary.IfaceName := iface2 "sockets" "network"
/-- `wasi:sockets/types@0.3.2`. -/
abbrev sockI3 : Binary.IfaceName := iface3 "sockets" "types"
/-- `wasi:http/types@0.2.12`. -/
abbrev httpI : Binary.IfaceName := iface2 "http" "types"
/-- `wasi:http/client@0.3.2`. -/
abbrev clientI3 : Binary.IfaceName := iface3 "http" "client"

/-- `finish-connect`. -/
abbrev sFinish : Binary.Sig := ⟨false, [("self", .borrow ⟨.local, "tcp-socket"⟩)],
  some (.result (some (.tuple [ownT "input-stream", ownT "output-stream"])) (some (refT "error-code")))⟩
/-- The 0.3 `connect`. -/
abbrev sConnect3 : Binary.Sig := ⟨true, [("self", .borrow ⟨.local, "tcp-socket"⟩),
  ("remote-address", refT "ip-socket-address")], some (.result none (some (refT "error-code")))⟩
/-- `future-incoming-response.get`. -/
abbrev sGet : Binary.Sig := ⟨false, [("self", .borrow ⟨.local, "future-incoming-response"⟩)],
  some (.option (.result (some (.result (some (ownT "incoming-response"))
    (some (refT "error-code")))) none))⟩

/-- The 0.3 `send`. -/
abbrev sSend3 : Binary.Sig := ⟨true, [("request", ownT "request")],
  some (.result (some (ownT "response")) (some (refT "error-code")))⟩

/-- **The resolved entries of the compared functions.** -/
theorem net_sigsR :
    sock2P.1.lookup Net.finishConnect = some (tcpI, sFinish) ∧
    sock3P.1.lookup Net.connect3 = some (sockI3, sConnect3) ∧
    http2P.1.lookup Net.futGet = some (httpI, sGet) ∧
    http3P.1.lookup Net.send3 = some (clientI3, sSend3) := by
  decide +kernel

theorem tcpErr_eq (n : Nat) (v : Val) :
    tyOkR sock2P.2 (n + 2) tcpI (refT "error-code") v = enumV 21 v := by
  have h1 : findTy sock2P.2 tcpI ⟨.local, "error-code"⟩ =
      some (tcpI, .type (.ref ⟨.iface netI, "error-code"⟩)) := by decide +kernel
  rw [tyOkR_ref h1, kindOk_type]
  exact tyOkR_enum (by decide +kernel) v

/-! ## 0.2 TCP -/

/-- A resolved answer value of `finish-connect`. -/
def finV : Val → Bool
  | .variant 0 (some p) => isPair p
  | .variant 1 (some e) => enumV 21 e
  | _ => false

/-- The resolved answers of `finish-connect`. -/
def finishAns : Option (List Val) → Bool
  | some [v] => finV v
  | _ => false

theorem resOkR_finish (r : Option (List Val)) :
    resOkR sock2P.2 tcpI sFinish r = finishAns r := by
  rw [resOkR_one, fuel_eq]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try rfl
  · rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | x⟩
    all_goals try rfl
    · simp only [tyOkR_result, resV, optOk, finishAns, finV]
      cases x <;> try rfl
      rename_i vs
      rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, vs⟩⟩⟩ <;> try rfl
      · cases a <;> rfl
      · cases a <;> cases b <;> rfl
      · cases a <;> cases b <;> rfl
    · simp only [tyOkR_result, resV, optOk, finishAns, finV, tcpErr_eq]

/-- **An accepted `finish-connect` answer on a pending socket is resolved-typed, for a typed
network.** -/
theorem tcpOk_witR (N : Net.Network) (hN : TypedNet N 21) (q : Net.TcpSt) (s : BitVec 32)
    (rest : List Val) (r : Option (List Val)) (hp : (Net.lookup s q).isSome = true)
    (h : Net.tcpOk N q (.imp Net.finishConnect (.u32 s :: rest) r) = true) :
    witROk (rrestrict sock2P [Net.finishConnect]) (.imp Net.finishConnect (.u32 s :: rest) r) =
      true := by
  have hres : finishAns r = true := by
    obtain ⟨addr, ha⟩ := Option.isSome_iff_exists.1 hp
    simp only [Net.tcpOk, ite_true, ha, Bool.or_eq_true] at h
    rcases h with h | h
    · unfold Net.isWouldBlock at h
      split at h
      · rfl
      · exact absurd h Bool.false_ne_true
    · unfold Net.connectOk at h
      split at h
      · rfl
      · rename_i k hk
        simp only [beq_iff_eq] at h
        subst h
        simp [finishAns, finV, enumV, hN addr _ hk]
      · exact absurd h Bool.false_ne_true
  simp [witROk, lookup_rrestrict, rrestrict_snd, net_sigsR.1, resOkR_finish, hres]

/-- A network failing with `21`, which is not a code. -/
def net21 : Net.Network := fun _ => some 21

/-- A `finish-connect` of a pending socket answered with the network's (non-)code. -/
def finish21 : WEv := .imp Net.finishConnect [.u32 0] (Net.errAnsN 21)

/-- **REFUTED for an untyped network**: the theory accepts its code `21`, which is not a
resolved `error-code`. -/
theorem tcpOk_not_witR_code :
    Net.tcpOk net21 [(0, .u32 0)] finish21 = true ∧
      witROk (rrestrict sock2P [Net.finishConnect]) finish21 = false := by
  decide +kernel

/-- A typed `finish-connect` answer `error(access-denied)` on an accepting network. -/
def finishDenied : WEv := .imp Net.finishConnect [.u32 0] (Net.errAnsN 1)

/-- **REFUTED converse**: resolved-typed, rejected by the theory of an accepting network. -/
theorem finish_witR_not_tcpOk :
    witROk (rrestrict sock2P [Net.finishConnect]) finishDenied = true ∧
      Net.tcpOk Net.netUp [(0, .u32 0)] finishDenied = false := by
  decide +kernel

/-! ## 0.3 TCP -/

/-- An IPv4 socket address `1.2.3.4:80`. -/
def sockAddr4 : Val := .variant 0 (some (.record [.u16 80, .record [.u8 1, .u8 2, .u8 3, .u8 4]]))

/-- A `connect` with resolved-typed arguments, answered `error(access-denied(true))`. -/
def connectJunk : WEv :=
  .imp Net.connect3 [.u32 0, sockAddr4] (some [errV (some (.variant 0 (some (.bool true))))])

/-- **REFUTED sound direction for 0.3 TCP**: the theory checks only the case of the error. -/
theorem tcpOk3_not_witR :
    Net.tcpOk3 (fun _ => some 0) () connectJunk = true ∧
      witROk (rrestrict sock3P [Net.connect3]) connectJunk = false := by
  decide +kernel

/-- The canonical 0.3 error values of the codes are resolved-typed. -/
theorem ecV3_witR : ∀ k, k < 15 →
    tyOkR sock3P.2 (fuel - 1) sockI3 (refT "error-code") (Net.ecV3 k) = true := by
  decide +kernel

theorem outcomeAns3_witR (o : Option Nat) (ho : ∀ k, o = some k → k < 15) :
    resOkR sock3P.2 sockI3 sConnect3 (Net.outcomeAns3 o) = true := by
  rw [resOkR_one, fuel_eq]
  cases o with
  | none => rfl
  | some k =>
    simp only [Net.outcomeAns3, errV, tyOkR_result, resV, optOk]
    exact ecV3_witR k (ho k rfl)

/-- **Restated: the concrete 0.3 TCP host answers `connect` with the resolved types**, for a
network whose codes are codes (traps admitted: a call without an address traps). -/
theorem tcpImpl3_witR (N3 : Net.Network) (hN : TypedNet N3 15) (p : List WEv) (a : List Val) :
    witRTrapOk (rrestrict sock3P [Net.connect3])
      (.imp Net.connect3 a (Net.tcpImpl3 N3 p Net.connect3 a)) = true := by
  have hc : Net.connect3 ≠ Net.create3 := by decide
  simp only [witRTrapOk, lookup_rrestrict, rrestrict_snd, List.mem_singleton, ite_true,
    net_sigsR.2.1]
  rcases a with _ | ⟨s, _ | ⟨addr, rest⟩⟩
  · simp [Net.tcpImpl3, hc]
  · simp [Net.tcpImpl3, hc]
  · simp only [Net.tcpImpl3, hc, ite_false, ite_true]
    rw [outcomeAns3_witR _ (fun k hk => hN addr k hk)]
    simp

/-- A typed `connect` answer `error(invalid-argument)` on an accepting network. -/
def connectInvalidR : WEv :=
  .imp Net.connect3 [.u32 0, sockAddr4] (some [errV (some (.variant 2 none))])

/-- **REFUTED converse**: resolved-typed, rejected by the theory of an accepting network. -/
theorem connect_witR_not_tcpTh3 :
    witROk (rrestrict sock3P [Net.connect3]) connectInvalidR = true ∧
      Net.tcpOk3 Net.netUp () connectInvalidR = false := by
  decide +kernel

/-! ## 0.2 HTTP -/

/-- **On a future of a request, an accepted `get` answer is resolved-typed, for a web that
never fails.** -/
theorem httpOk_witR_up (W : Net.Web) (hW : WebUp W) (q : Net.HttpSt) (h0 : BitVec 32)
    (rest : List Val) (r : Option (List Val)) (hp : (Net.lookup h0 q.futs).isSome = true)
    (h : Net.httpOk W q (.imp Net.futGet (.u32 h0 :: rest) r) = true) :
    witROk (rrestrict http2P [Net.futGet]) (.imp Net.futGet (.u32 h0 :: rest) r) = true := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hp
  simp only [Net.httpOk, ite_true, hk] at h
  have hres : resOkR http2P.2 httpI sGet r = true := by
    rw [resOkR_one, fuel_eq]
    unfold Net.getOk at h
    split at h
    · rfl
    · rfl
    · rename_i x
      obtain ⟨s, hs⟩ := hW k.1 k.2
      rw [hs] at h
      unfold Net.outcomeOk at h
      split at h
      all_goals first | rfl | exact absurd h Bool.false_ne_true | exact absurd ‹Net.HttpOutcome.status _ = Net.HttpOutcome.error _› (fun h => nomatch h)
    · exact absurd h Bool.false_ne_true
  simp [witROk, lookup_rrestrict, rrestrict_snd, net_sigsR.2.2.1, hres]

/-- A `get` answer `some(ok(error(DNS-timeout(true))))` on a future of a request. -/
def getJunk : WEv := .imp Net.futGet [.u32 0]
  (some [.variant 1 (some (.variant 0 (some (errV (some (.variant 0 (some (.bool true))))))))])

/-- The state with the future `0` of the request `(none, none)`. -/
def futState : Net.HttpSt := { Net.HttpSt.init with futs := [(0, (Net.noneV, Net.noneV))] }

/-- **REFUTED for a failing web**: the theory checks only the case of the error. -/
theorem httpOk_not_witR :
    Net.httpOk Net.webDown futState getJunk = true ∧
      witROk (rrestrict http2P [Net.futGet]) getJunk = false := by
  decide +kernel

/-! ## 0.3 HTTP -/

/-- **An accepted `send` answer is resolved-typed or a trap, for a web that never fails.** -/
theorem http3Ok_witR_up (W : Net.Web) (hW : WebUp W) (q : Net.Http3St) (r0 : BitVec 32)
    (rest : List Val) (r : Option (List Val))
    (h : Net.http3Ok W q (.imp Net.send3 (.u32 r0 :: rest) r) = true) :
    witRTrapOk (rrestrict http3P [Net.send3]) (.imp Net.send3 (.u32 r0 :: rest) r) = true := by
  simp only [witRTrapOk, lookup_rrestrict, rrestrict_snd, List.mem_singleton, ite_true,
    net_sigsR.2.2.2]
  simp only [Net.http3Ok, ite_true, Bool.or_eq_true] at h
  rcases h with h | h
  · simp [h]
  · obtain ⟨st, hst⟩ := hW (q.key r0).1 (q.key r0).2
    rw [hst] at h
    unfold Net.sendOk at h
    split at h
    all_goals first
      | exact absurd h Bool.false_ne_true
      | exact absurd ‹Net.HttpOutcome.status _ = Net.HttpOutcome.error _› (fun h => nomatch h)
      | simp [resOkR, fuel_eq, tyOkR_result, resV, optOk, tyOkR_own, isU32]

/-- A `send` with the answer `error(DNS-timeout(true))`. -/
def sendJunk : WEv := .imp Net.send3 [.u32 0]
  (some [errV (some (.variant 0 (some (.bool true))))])

/-- **REFUTED for a failing web**. -/
theorem http3Ok_not_witR :
    Net.http3Ok Net.webDown {} sendJunk = true ∧
      witROk (rrestrict http3P [Net.send3]) sendJunk = false := by
  decide +kernel

/-- A typed `send` answer `error(DNS-timeout)` on a web that answers `200`. -/
def sendTimeout : WEv := .imp Net.send3 [.u32 0] (some [errV (some (.variant 0 none))])

/-- **REFUTED converse**: resolved-typed, rejected by the theory of the web `webUp`. -/
theorem send_witR_not_http3 :
    witROk (rrestrict http3P [Net.send3]) sendTimeout = true ∧
      Net.http3Ok Net.webUp {} sendTimeout = false := by
  decide +kernel

/-! ## The concrete hosts' error answers -/

/-- The HTTP error codes whose case has no payload. -/
def httpFree : List Nat :=
  [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 18, 19, 20, 25, 33, 34, 35, 36, 37]

/-- **For a payload-free code the hosts' error answers are resolved-typed**, in both versions. -/
theorem httpAns_witR : ∀ k ∈ httpFree,
    tyOkR http2P.2 (fuel - 2) httpI (refT "error-code") (.variant k none) = true ∧
    tyOkR http3P.2 (fuel - 2) clientI3 (refT "error-code") (.variant k none) = true := by
  decide +kernel

/-- **The concrete hosts answer `TLS-alert-received` without its payload**, which is not a
resolved `error-code` in either version. -/
theorem httpAns_not_witR :
    tyOkR http2P.2 (fuel - 2) httpI (refT "error-code") (.variant 14 none) = false ∧
    tyOkR http3P.2 (fuel - 2) clientI3 (refT "error-code") (.variant 14 none) = false ∧
    Net.sendAns 0 (.error 14) = some [errV (some (.variant 14 none))] :=
  ⟨by decide +kernel, by decide +kernel, rfl⟩

/-- `webDown`'s answer to `send` (`DNS-timeout`) is resolved-typed. -/
theorem sendAns_witR :
    witROk (rrestrict http3P [Net.send3]) (.imp Net.send3 [.u32 0] (Net.sendAns 0 (.error 0))) =
      true := by
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
