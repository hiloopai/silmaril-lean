module

public import Silmaril.Wasi.Versions.WitImport.Http3Table.Defs
public import Silmaril.Wasi.Versions.WitImport.NetTyping.Thms
public import Silmaril.Wasi.Versions.Http3.Defs

/-!
# The hand-written `wasi:http` 0.3 theory against the imported `wasi:http@0.3.2`

`http3T` (`Silmaril.Wasi.Versions.WitImport.Http3Table`) is read out of `http/worlds.wit` (the
interfaces `handler` and `client`, worlds dropped) and `http/types.wit`.

* **Names**: `http3_mem`, `http3Fns_sub`: the four functions of `Silmaril.Wasi.Versions.Http3`
  (`client.send`, `request.set-authority`, `request.set-path-with-query`,
  `response.get-status-code`) are imported functions; `http3_async`: of these only `send` is
  `async` (observed sync-lowered, as the slice says); `handle_send_sig`: the export
  `handler.handle` has the signature of `client.send`, as the slice's docstring says.
* **Signatures** `http3_sigs`: the hand-written docstring of `Http3` is the imported WIT
  (`send(request: own<request>) -> result<own<response>, error-code>`,
  `set-authority(self, authority: option<string>) -> result`, the same for
  `set-path-with-query`, `get-status-code(self) -> status-code`).
* **Typing** `httpTh3_wit`: every trace of `Net.httpTh3 W` is WIT-typed for `send`, traps
  admitted.
* **REFUTED** for the setters (`setAuth3_not_wit`): `Net.httpTh3` leaves `set-authority`
  unconstrained, so it accepts answers that are not a `result`. **REFUTED converse**
  (`send_wit_not_httpTh3`): a WIT-typed `send` error is rejected by the theory of `webUp`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Resource (Protocol)

/-- The 0.3 HTTP functions of the hand-written theory are imported functions. -/
theorem http3_mem : ∀ f ∈ [Net.send3, Net.setAuth3, Net.setPath3, Net.getStatus3],
    f ∈ names http3T := by
  decide +kernel

/-- The hand-written 0.3 HTTP functions are imported functions. -/
theorem http3Fns_sub : Net.http3Fns ⊆ {f | f ∈ names http3T} := by
  intro f hf
  exact http3_mem f (by simpa [Net.http3Fns_eq] using hf)

/-- Of these, only `send` is `async` in the WIT. -/
theorem http3_async : [Net.send3, Net.setAuth3, Net.setPath3, Net.getStatus3].filter
    (fun f => (http3T.lookup f).any (·.async)) = [Net.send3] := by
  decide +kernel

/-- `handler.handle` has the signature of `client.send`. -/
theorem handle_send_sig :
    http3T.lookup ⟨"wasi:http/handler@0.3.2", "handle"⟩ = http3T.lookup Net.send3 := by
  decide +kernel

/-- **The imported signatures of the 0.3 HTTP slice.** -/
theorem http3_sigs :
    http3T.lookup Net.send3 = some ⟨true, [("request", ownT "request")],
      some (.result (some (ownT "response")) (some (refT "error-code")))⟩ ∧
    http3T.lookup Net.setAuth3 = some ⟨false, [("self", .borrow ⟨.local, "request"⟩),
      ("authority", .option tStr)], some (.result none none)⟩ ∧
    http3T.lookup Net.setPath3 = some ⟨false, [("self", .borrow ⟨.local, "request"⟩),
      ("path-with-query", .option tStr)], some (.result none none)⟩ ∧
    http3T.lookup Net.getStatus3 = some ⟨false, [("self", .borrow ⟨.local, "response"⟩)],
      some (refT "status-code")⟩ := by
  decide +kernel

theorem sendOk_res {o : Net.HttpOutcome} {r : Option (List Val)} (h : Net.sendOk o r = true) :
    resOk ⟨true, [("request", ownT "request")],
      some (.result (some (ownT "response")) (some (refT "error-code")))⟩ r = true := by
  unfold Net.sendOk at h
  split at h <;> simp_all [resOk, tyOk, tyOpt]

theorem http3Ok_wit (W : Net.Web) (q : Net.Http3St) (e : WEv) (h : Net.http3Ok W q e = true) :
    witTrapOk (restrict http3T [Net.send3]) e = true := by
  cases e with
  | imp f a r =>
    by_cases hf : f = Net.send3
    · subst hf
      simp only [witTrapOk, lookup_restrict, List.mem_singleton, ite_true, http3_sigs.1]
      rcases a with _ | ⟨v, _ | ⟨w, rest⟩⟩
      · simp [argsOk, tysOk]
      · cases v
        case u32 x =>
          simp only [Net.http3Ok, ite_true, Bool.or_eq_true] at h
          rcases h with h | h
          · simp [h]
          · simp [sendOk_res h]
        all_goals simp [argsOk, tysOk, tyOk]
      · simp [argsOk, tysOk]
    · simp [witTrapOk, lookup_restrict, hf]
  | _ => rfl

/-- **The 0.3 HTTP theory implies the imported WIT typing of `send` (traps admitted).** -/
theorem httpTh3_wit (W : Net.Web) {t : List WEv} (h : (Net.httpTh3 W).Accepts t) :
    (witTrapTh (restrict http3T [Net.send3])).Accepts t :=
  accepts_pointwise _ _ (fun q e _ hs => http3Ok_wit W q e (gated_step_ok hs)) h

/-- A `set-authority` answer that is not a `result`. -/
def setAuthBad : WEv := .imp Net.setAuth3 [.u32 0, .variant 0 none] (some [])

/-- **REFUTED for the setters**: the theory accepts an answer that is not WIT-typed. -/
theorem setAuth3_not_wit :
    Net.http3Ok Net.webUp {} setAuthBad = true ∧
      witOk (restrict http3T [Net.setAuth3]) setAuthBad = false := by
  decide +kernel

/-- A WIT-typed `send` answer `error(DNS-timeout)`. -/
def sendDnsErr : WEv := .imp Net.send3 [.u32 0] (some [errV (some (.variant 0 none))])

/-- **REFUTED converse**: the WIT typing accepts a `send` error the theory of `webUp`
rejects. -/
theorem send_wit_not_httpTh3 :
    witOk (restrict http3T [Net.send3]) sendDnsErr = true ∧
      Net.http3Ok Net.webUp {} sendDnsErr = false := by
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
