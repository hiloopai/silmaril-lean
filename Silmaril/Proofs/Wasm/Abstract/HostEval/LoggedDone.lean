module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.LoggedWhole

/-!
# Exact-log finished behaviours of invocations, backward (proofs)

`invoke_doneL`: in the deterministic profile `SingleThreaded.profile o`, for a host with typed
answers (`HostTyped`) in the native host slice, a labelled Core run of a typed invocation of a
checked store, with its exact host-event log `cs`, to values or to a trap is the finished
behaviour of the logged closed semantics `wasmEvFun` **with exactly that log**: values `ws`
are `(cs, ret (inl ws) s₂)` at the run's final store `s₂` (in the empty frame), a trap is
`(cs, trap)`. From `back_callRef_wasmL` (a Wasm callee; `back_wholeL` on its body) and the one
host event of a host callee (`close_host`): a returning body is a closed behaviour by
`close_wasm`, a trapping one by `close_of_trapT`.

`evRun_wasmEvFun_vals`, `evRun_wasmEvFun_trap`: the same for `EvRun`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H} {o : GrowOracle}

theorem vals_ne_trap {ws : List Val} : vals ws ≠ [.trap] := fun h =>
  absurd (h ▸ (by simp : Admin.trap ∈ [Admin.trap])) (not_mem_vals_of_val? (a := .trap) rfl)

/-- **Exact-log finished behaviours of an invocation** (deterministic profile): a labelled
Core run of a typed invocation, with its log `cs`, to values ends in the empty frame and is the
returning behaviour `(cs, ret (inl ws) c.store)` of `wasmEvFun`; to a trap, it is the trapping
behaviour `(cs, trap)`. -/
theorem invoke_doneL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {s : Store H} {a : Nat} {vs : List Val} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : EvRunN (profile o) host n (invoke s a vs) cs c)
    (hc : (∃ ws, c.code = vals ws) ∨ c.code = [.trap]) :
    (∀ ws, c.code = vals ws → c.frame = {} ∧ (cs, .ret (.inl ws) c.store) ∈ wasmEvFun s (a, vs)) ∧
      (c.code = [.trap] → (cs, .trap) ∈ wasmEvFun s (a, vs)) := by
  have hend : ∀ c', ¬ Step (profile o) Det.noHost c c' := by
    obtain ⟨cst, cf, cc⟩ := c
    rcases hc with ⟨ws, hw⟩ | hw <;> dsimp only at hw <;> subst hw
    · exact fun c' => Sim.Step.not_vals
    · exact fun c' => Step.trap_stuck
  have hnat : ∀ m, ¬ AtHost c m := by
    intro m hat
    rcases hc with ⟨ws, hw⟩ | hw
    · exact atHost_ne_vals hat ws hw
    · exact atHost_ne_trap hat hw
  obtain ⟨-, -, rts, -, -, hcok⟩ := invoke_ok hs hok
  obtain ⟨fi, ps', rs', hfi, he, hvt⟩ := hok
  have hty := Interp.funcType_of_expand he
  have hlen : vs.length = ps'.toList.length :=
    Interp.args_length ⟨fi, ps', rs', hfi, he, hvt⟩ hfi hty
  have hcode₀ : (invoke s a vs).code =
      vals vs.reverse.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ []) := by
    simp [invoke, hfi]
  have hrun' : EvRunN (profile o) host n
      ⟨s, {}, vals vs.reverse.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ [])⟩ cs c := by
    rw [← hcode₀]; exact hrun
  cases hcd : fi.code with
  | host hh =>
    have hrun'' : EvRunN (profile o) host n
        ⟨s, {}, vals [] ++ vals vs ++ .ref (.func a) :: .callRefType fi.type :: []⟩ cs c := by
      simpa using hrun'
    have hn : vs.length = ps'.length := by simpa [Validation.Ty.length] using hlen
    rcases evRunN_host_call hfi hcd he hn hrun'' with ⟨rfl, rfl⟩ |
        ⟨s', r, m', cs', -, rfl, hhost, hk⟩
    · exact (hnat _ (atHost_call (ws := []) (rest := []) hfi hcd he hn)).elim
    · rcases r with ws | t | _
      · obtain ⟨rfl, rfl⟩ := evRunN_of_stuck (fun c' => Sim.Step.not_vals (vs := ws))
          (by simpa [Result.toAdmin] using hk)
        have hw := hH.arity s a fi hh _ _ vs ws s' hfi hcd hty hhost
        refine ⟨fun ws' hws' => ⟨rfl, ?_⟩, fun h => (vals_ne_trap h).elim⟩
        obtain rfl : ws' = ws := (Sim.vals_injective hws').symm
        have hx : exitFlow rs'.toList.length (resFlow (.values ws')) = some (.normal ws') := by
          simp only [resFlow, exitFlow, Option.some.injEq, Binaryen.Flow.normal.injEq]
          rw [List.take_of_length_le (by simp [hw])]
          simp
        exact close_host (us := vs) (s' := s') hfi hcd hty hx
      · exact (hH.noThrow hh s vs s' t hhost).elim
      · obtain ⟨rfl, rfl⟩ := evRunN_of_stuck (fun c' => Step.trap_stuck)
          (by simpa [Result.toAdmin] using hk)
        refine ⟨fun ws hws => (vals_ne_trap hws.symm).elim, fun _ => ?_⟩
        exact close_host (us := vs) (s' := s') (r := .trap) (fl := .trap) hfi hcd hty rfl
  | wasm fn =>
    have hp : ps'.toList.length ≤ vs.reverse.length := by simp [hlen]
    have htake : (vs.reverse.take ps'.toList.length).reverse = vs := by
      rw [List.take_of_length_le (by simp [hlen])]; simp
    have hdrop : vs.reverse.drop ps'.toList.length = [] := by simp [hlen]
    have hframe : Interp.calleeFrame fi fn vs.reverse ps'.toList.length =
        Frame.forCall fi.module vs fn.locals := by
      simp [Interp.calleeFrame, htake]
    obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq (hS a fi fn _ _ hfi hcd hty)
    have hbc : Interp.chk s.funcs (Frame.forCall fi.module vs fn.locals).module
        (Frame.forCall fi.module vs fn.locals).locals.length rs'.toList.length [rs'.toList.length]
        (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
      rw [Interp.forCall_length _ _ hlen]; exact hb
    have hct : Sim.ContextTyped ⟨s, Frame.forCall fi.module vs fn.locals,
        vals ([] : List Val).reverse ++
          expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ := by
      have enter := Interp.steps_invoke_enter (P := profile o) (host := Det.noHost) hfi hcd hty
        hlen
      have h₁ := Sim.ContextTyped.frame (vs := []) (rest := [])
        (by simpa [vals] using Sim.ContextTyped.steps (Sim.ContextTyped.of_configOk hcok) enter)
      have h₂ := Sim.ContextTyped.label (vs := []) (rest := []) (by simpa [vals] using h₁)
      simpa [Binaryen.lowerList_liftInstrs, vals] using h₂
    rcases back_callRef_wasmL (o := o) hfi hcd hty hp hrun' hend
        (fun m _ cb cs₁ h hsb => by
          rw [hframe] at h ⊢
          exact back_wholeL hT hH m _ s _ [] [rs'.toList.length] rs'.toList.length ob cb cs₁ hS
            hbc hct h hsb)
        (fun r hev => by
          rw [hframe] at hev
          obtain ⟨hok', -⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hbc
          refine ⟨fun ws hws => ⟨Interp.retVals_length hok' hob hws, fun ws' hws' => by
            rw [hws'] at hok'; exact Interp.length_of_ends hok' hob⟩, fun hn => ?_⟩
          rcases hfl : r.2.2 with ws | ⟨_ | k, ws⟩ | ws | _ | t <;> rw [hfl] at hok' hn <;>
            simp_all [Binaryen.Flow.retVals, Interp.FlowOkE]) with ⟨mm, hat', -⟩ |
      ⟨s₂, fl, q, cs', rfl, -, hmem, hmt, ⟨ws, m', -, hws, hk⟩ | ⟨rfl, hends, rfl⟩⟩
    · exact (hnat _ hat').elim
    · rw [hdrop] at hk
      obtain ⟨rfl, rfl⟩ := evRunN_of_stuck (fun c' => Sim.Step.not_vals) (by simpa using hk)
      refine ⟨fun ws' hws' => ⟨rfl, ?_⟩, fun h => (vals_ne_trap h).elim⟩
      obtain rfl : ws' = (ws.take rs'.toList.length).reverse :=
        (Sim.vals_injective (by simpa using hws')).symm
      have := hmem ws hws
      rw [htake, ← List.append_nil q] at this
      exact this
    · obtain ⟨oc, he', hst, hfr, hm⟩ := hends
      rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm
      have hc' : c.code = [.trap] := he'
      refine ⟨fun ws hws => (vals_ne_trap (hws.symm.trans hc')).elim, fun _ => ?_⟩
      have := hmt rfl
      rw [htake, ← List.append_nil q] at this
      exact this

/-- **Values, with exactly the run's log** (deterministic profile, typed checked
invocations): a Core run of the invocation with the host events `cs` to the values `ws` at the
store `s₂` is the returning behaviour `(cs, ret (inl ws) s₂)` of `wasmEvFun`. -/
theorem evRun_wasmEvFun_vals (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s s₂ : Store H} {a : Nat} {vs ws : List Val} {f₂ : Frame}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, vals ws⟩) :
    (cs, .ret (.inl ws) s₂) ∈ wasmEvFun s (a, vs) := by
  obtain ⟨n, hn⟩ := evRunN_of_evRun hrun
  exact ((invoke_doneL hT hH hs hS hok hn (.inl ⟨ws, rfl⟩)).1 ws rfl).2

/-- **The frame of a finished run**: a Core run of a typed checked invocation to values ends in
the empty frame (deterministic profile). -/
theorem evRun_vals_frame (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s s₂ : Store H} {a : Nat} {vs ws : List Val} {f₂ : Frame}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, vals ws⟩) : f₂ = {} := by
  obtain ⟨n, hn⟩ := evRunN_of_evRun hrun
  exact ((invoke_doneL hT hH hs hS hok hn (.inl ⟨ws, rfl⟩)).1 ws rfl).1

/-- **A trap, with exactly the run's log** (deterministic profile, typed checked invocations): a
Core run of the invocation with the host events `cs` to a trap is the trapping behaviour
`(cs, trap)` of `wasmEvFun`. -/
theorem evRun_wasmEvFun_trap (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s s₂ : Store H} {a : Nat} {vs : List Val} {f₂ : Frame}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, [.trap]⟩) :
    (cs, .trap) ∈ wasmEvFun s (a, vs) := by
  obtain ⟨n, hn⟩ := evRunN_of_evRun hrun
  exact (invoke_doneL hT hH hs hS hok hn (.inr rfl)).2 rfl

end Silmaril.Proofs.Wasm.Abstract.HostEval
