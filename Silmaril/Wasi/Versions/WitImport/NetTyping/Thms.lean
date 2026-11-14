module

public import Silmaril.Wasi.Versions.WitImport.Cli2.Thms
public import Silmaril.Wasi.Versions.WitImport.NetNames.Thms

/-!
# The hand-written `wasi:sockets` and `wasi:http` 0.2 theories, and 0.3 sockets, against the
imported signatures

The network theories (`Silmaril.Wasi.Versions.Net`, `Net3`, `NetMore`) are behavioural: they
check the answers of a few functions against a network, a web or a resolver, and only in some
states. The typing comparison is therefore stated where they check:

* **0.3 TCP** (`tcpTh3_wit`): every trace of `Net.tcpTh3 N3` is WIT-typed for `connect`, traps
  admitted (`connect: async func(remote-address: ip-socket-address) -> result<_, error-code>`).
* **0.2 TCP** (`tcpOk_wit`): an answer of `finish-connect` on a *pending* socket accepted by
  `Net.tcpOk N` is WIT-typed (`result<tuple<own<input-stream>, own<output-stream>>,
  error-code>`). **REFUTED** without the pending condition (`tcpOk_not_wit`: on a socket
  without a `start-connect`, the theory accepts any answer).
* **0.2 HTTP** (`httpOk_wit`): an answer of `future-incoming-response.get` on a future of a
  request accepted by `Net.httpOk W` is WIT-typed
  (`option<result<result<incoming-response, error-code>>>`).
* **0.3 name lookup**: **REFUTED** (`dnsTh3_not_wit`): `NetMore.dnsTh3` accepts every
  answer that is not `ok(list)`, so it accepts answers that are not of the WIT type
  `result<list<ip-address>, error-code>`.

The converse direction fails everywhere the WIT type is a named one (`error-code`,
`ip-socket-address`): `tyOk` accepts any value there, and the theories pin the error code to
the network's outcome (`connect_wit_not_tcpTh3`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Resource (Protocol)

theorem gated_step_ok {S : Type} {init : S} {next : S → WEv → S} {ok : S → WEv → Bool}
    {q q' : S} {e : WEv} (h : (Net.gated init next ok).step q e = some q') : ok q e = true := by
  simp only [Net.gated] at h
  split at h
  · assumption
  · cases h

/-! ## Signatures -/

/-- The imported signatures of `connect` (0.3), `finish-connect` and `get` (0.2). -/
theorem net_sigs :
    sock3T.lookup Net.connect3 = some ⟨true, [("self", .borrow ⟨.local, "tcp-socket"⟩),
      ("remote-address", refT "ip-socket-address")], some (.result none (some (refT "error-code")))⟩ ∧
    ResIs sock2T Net.finishConnect
      (some (.result (some (.tuple [ownT "input-stream", ownT "output-stream"]))
        (some (refT "error-code")))) ∧
    ResIs http2T Net.futGet
      (some (.option (.result (some (.result (some (ownT "incoming-response"))
        (some (refT "error-code")))) none))) := by
  decide +kernel

/-! ## 0.3 TCP -/

theorem connectOk3_res {o : Option Nat} {r : Option (List Val)} {b : Bool}
    {ps : List (String × Binary.Ty)} {x : Binary.TyRef} (h : Net.connectOk3 o r = true) :
    resOk ⟨b, ps, some (.result none (some (.ref x)))⟩ r = true := by
  unfold Net.connectOk3 at h
  split at h <;> simp_all [resOk, tyOk, tyOpt]

theorem tcpOk3_wit (N3 : Net.Network) (e : WEv) (h : Net.tcpOk3 N3 () e = true) :
    witTrapOk (restrict sock3T [Net.connect3]) e = true := by
  cases e with
  | imp f a r =>
    by_cases hf : f = Net.connect3
    · subst hf
      simp only [witTrapOk, lookup_restrict, List.mem_singleton, ite_true, net_sigs.1]
      rcases a with _ | ⟨s, _ | ⟨addr, rest⟩⟩
      · simp [argsOk, tysOk]
      · simp [argsOk, tysOk]
      · simp only [Net.tcpOk3, ite_true, Bool.or_eq_true] at h
        rcases h with h | h
        · simp [h]
        · simp [connectOk3_res h]
    · simp [witTrapOk, lookup_restrict, hf]
  | _ => rfl

/-- **The 0.3 TCP theory implies the imported WIT typing of `connect` (traps admitted).** -/
theorem tcpTh3_wit (N3 : Net.Network) {t : List WEv} (h : (Net.tcpTh3 N3).Accepts t) :
    (witTrapTh (restrict sock3T [Net.connect3])).Accepts t :=
  accepts_pointwise _ _ (fun _ e _ hs => tcpOk3_wit N3 e (gated_step_ok hs)) h

/-- A WIT-typed `connect` answer `error(invalid-argument)` on an accepting network. -/
def connectInvalid : WEv :=
  .imp Net.connect3 [.u32 0, .record []] (some [errV (some (.variant 2 none))])

/-- **REFUTED converse**: the WIT typing accepts an error the theory of an accepting network
rejects. -/
theorem connect_wit_not_tcpTh3 :
    witOk (restrict sock3T [Net.connect3]) connectInvalid = true ∧
      Net.tcpOk3 Net.netUp () connectInvalid = false := by
  decide +kernel

/-! ## 0.2 TCP and HTTP -/

theorem connectOk_res {o : Option Nat} {r : Option (List Val)} (h : Net.connectOk o r = true) :
    resOk ⟨false, [], some (.result (some (.tuple [ownT "input-stream", ownT "output-stream"]))
      (some (refT "error-code")))⟩ r = true := by
  unfold Net.connectOk at h
  split at h <;> simp_all [resOk, tyOk, tyOpt, tysOk]

/-- **An accepted `finish-connect` answer on a pending socket is WIT-typed.** -/
theorem tcpOk_wit (N : Net.Network) (q : Net.TcpSt) (s : BitVec 32) (rest : List Val)
    (r : Option (List Val)) (hp : (Net.lookup s q).isSome = true)
    (h : Net.tcpOk N q (.imp Net.finishConnect (.u32 s :: rest) r) = true) :
    witOk (restrict sock2T [Net.finishConnect]) (.imp Net.finishConnect (.u32 s :: rest) r) =
      true := by
  refine witOk_of (by simp) net_sigs.2.1 ?_
  obtain ⟨addr, ha⟩ := Option.isSome_iff_exists.1 hp
  simp only [Net.tcpOk, ite_true, ha, Bool.or_eq_true] at h
  rcases h with h | h
  · unfold Net.isWouldBlock at h
    split at h <;> simp_all [resOk, tyOk, tyOpt]
  · exact connectOk_res h

/-- A `finish-connect` answer that is not a `result`, on a socket without `start-connect`. -/
def finishBad : WEv := .imp Net.finishConnect [.u32 0] (some [])

/-- **REFUTED without the pending condition.** -/
theorem tcpOk_not_wit :
    Net.tcpOk Net.netUp [] finishBad = true ∧
      witOk (restrict sock2T [Net.finishConnect]) finishBad = false := by
  decide +kernel

theorem getOk_res {W : Net.Web} {k : Val × Val} {r : Option (List Val)}
    (h : Net.getOk W k r = true) :
    resOk ⟨false, [], some (.option (.result (some (.result (some (ownT "incoming-response"))
      (some (refT "error-code")))) none))⟩ r = true := by
  unfold Net.getOk at h
  split at h
  · simp [resOk, tyOk]
  · simp [resOk, tyOk, tyOpt]
  · rename_i x
    unfold Net.outcomeOk at h
    split at h <;> simp_all [resOk, tyOk, tyOpt]
  · exact absurd h Bool.false_ne_true

/-- **An accepted `get` answer on a future of a request is WIT-typed.** -/
theorem httpOk_wit (W : Net.Web) (q : Net.HttpSt) (h0 : BitVec 32) (rest : List Val)
    (r : Option (List Val)) (hp : (Net.lookup h0 q.futs).isSome = true)
    (h : Net.httpOk W q (.imp Net.futGet (.u32 h0 :: rest) r) = true) :
    witOk (restrict http2T [Net.futGet]) (.imp Net.futGet (.u32 h0 :: rest) r) = true := by
  refine witOk_of (by simp) net_sigs.2.2 ?_
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hp
  simp only [Net.httpOk, ite_true, hk] at h
  exact getOk_res h

/-! ## 0.3 name lookup -/

/-- A `resolve-addresses` answer that is not a `result`. -/
def resolveBad : WEv := .imp Net.resolve3 [strV "a"] (some [])

/-- **REFUTED for the 0.3 name lookup**: the theory accepts an answer that is not WIT-typed. -/
theorem dnsTh3_not_wit :
    Net.dnsOk3 Net.dnsEmpty () resolveBad = true ∧
      witOk (restrict sock3T [Net.resolve3]) resolveBad = false := by
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
