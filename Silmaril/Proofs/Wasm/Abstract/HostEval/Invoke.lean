module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.Obs

/-!
# The backward simulation of an invocation (proofs)

`back_invoke`, deterministic profile: a Core run of a typed invocation
`invoke s a vs` of a store whose functions pass the arity check, to a stuck end,
for a host with typed answers in the native host slice, is blocked at a host call
(`Pending`), or ends exactly as a native answer for the call does
(`hostCall host s a vs`): the callee's results, or a trap, in the answer's store.
A host function is read off the run (`host_call_runN_seq`); a Wasm function's
body is given by `back_whole` (`back_callRef_wasm`).

`back_invoke_reach` adds reach evidence: the blocked call is the invoked host function
itself, or a pending call (`PendO`) of the invoked Wasm function. Both are read off
`back_invoke_core`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

/-- **The backward simulation of an invocation, with reach evidence** (deterministic
profile): both the blocked call (`Pending`) and how the native semantics reaches it. -/
theorem back_invoke_core {o : GrowOracle} (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {n : Nat} {s : Store H} {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s)
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN (profile o) host n (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (profile o) host c c') :
    (Pending host c.store c.code ∧ ∃ y : (wasmOShape H).self.Op,
        (y = ⟨a, (vs, s)⟩ ∨ PendO (hostCall host) ⟨a, (vs, s)⟩ y) ∧ BlockedAt host c y) ∨
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow),
        s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        hostCall host s a vs (s₂, fl) ∧
        ((∃ ws, fl.retVals = some ws ∧ c = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
          (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) := by
  obtain ⟨-, -, rts, -, -, hcok⟩ := invoke_ok hs hok
  obtain ⟨fi, ps', rs', hfi, he, hvt⟩ := hok
  have hty := Interp.funcType_of_expand he
  have hlen : vs.length = ps'.toList.length :=
    Interp.args_length ⟨fi, ps', rs', hfi, he, hvt⟩ hfi hty
  have hcode₀ : (invoke s a vs).code =
      vals vs.reverse.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ []) := by
    simp [invoke, hfi]
  have hrun' : StepsN (profile o) host n
      ⟨s, {}, vals vs.reverse.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ [])⟩ c := by
    rw [← hcode₀]; exact hrun
  cases hcd : fi.code with
  | host hh =>
    have hrun'' : StepsN (profile o) host n
        ⟨s, {}, vals [] ++ vals vs ++ .ref (.func a) :: .callRefType fi.type :: []⟩ c := by
      simpa using hrun'
    have hn : vs.length = ps'.length := by simpa [Validation.Ty.length] using hlen
    rcases host_call_runN_seq hfi hcd he hn hrun'' hend with ⟨rfl, hno⟩ |
        ⟨s', r, m, -, hhost, hk⟩
    · exact .inl ⟨Pending.call (ws := []) hfi hcd he hn hno, _, .inl rfl, fi, hh, rfl, hfi, hcd,
        hno, AtCall.here (ws := []) hfi⟩
    · right
      have hcall : hostCall host s a vs (s', resFlow r) := by
        rw [hostCall_fixpoint]
        exact .inr ⟨fi, hh, r, hfi, hcd, hhost, rfl⟩
      refine ⟨fi, _, _, s', resFlow r, hfi, hty, hcall, ?_⟩
      rcases r with ws | t | _
      · left
        have hl := hH.arity s a fi hh _ _ vs ws s' hfi hcd hty hhost
        have hc := stepsN_of_stuck (fun c' => Sim.Step.not_vals (vs := ws))
          (by simpa [Result.toAdmin] using hk)
        refine ⟨ws.reverse, rfl, ?_⟩
        rw [hc, List.take_of_length_le (by simp [hl])]
        simp
      · exact (hH.noThrow hh s vs s' t hhost).elim
      · right
        exact ⟨rfl, stepsN_of_stuck (fun c' => Step.trap_stuck) (by simpa [Result.toAdmin] using hk)⟩
  | wasm fn =>
    have hp : ps'.toList.length ≤ vs.reverse.length := by simp [hlen]
    have htake : (vs.reverse.take ps'.toList.length).reverse = vs := by
      rw [List.take_of_length_le (by simp [hlen])]; simp
    have hdrop : vs.reverse.drop ps'.toList.length = [] := by simp [hlen]
    have hframe : Interp.calleeFrame fi fn vs.reverse ps'.toList.length =
        Frame.forCall fi.module vs fn.locals := by
      simp [Interp.calleeFrame, htake]
    -- the callee body: checked and typed
    obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq (hS a fi fn _ _ hfi hcd hty)
    have hbc : Interp.chk s.funcs (Frame.forCall fi.module vs fn.locals).module
        (Frame.forCall fi.module vs fn.locals).locals.length rs'.toList.length [rs'.toList.length]
        (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
      rw [Interp.forCall_length _ _ hlen]; exact hb
    have hct : Sim.ContextTyped ⟨s, Frame.forCall fi.module vs fn.locals,
        vals ([] : List Val).reverse ++
          expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ := by
      have enter := Interp.steps_invoke_enter (P := profile o) (host := Det.noHost) hfi hcd hty hlen
      have h₁ := Sim.ContextTyped.frame (vs := []) (rest := [])
        (by simpa [vals] using Sim.ContextTyped.steps (Sim.ContextTyped.of_configOk hcok) enter)
      have h₂ := Sim.ContextTyped.label (vs := []) (rest := []) (by simpa [vals] using h₁)
      simpa [Binaryen.lowerList_liftInstrs, vals] using h₂
    rcases back_callRef_wasm (o := o) hfi hcd hty hp hrun' hend
        (fun m _ cb h hsb => by
          rw [hframe] at h ⊢
          exact back_whole hT hH m _ s _ [] [rs'.toList.length] rs'.toList.length ob cb hS hbc hct
            h hsb)
        (fun r hev => by
          rw [hframe] at hev
          obtain ⟨hok', -⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hbc
          refine ⟨fun ws hws => ⟨Interp.retVals_length hok' hob hws, fun ws' hws' => by
            rw [hws'] at hok'; exact Interp.length_of_ends hok' hob⟩, fun hn => ?_⟩
          rcases hfl : r.2.2 with ws | ⟨_ | k, ws⟩ | ws | _ | t <;> rw [hfl] at hok' hn <;>
            simp_all [Binaryen.Flow.retVals, Interp.FlowOk]) with ⟨hpend, y, hy, hb⟩ |
      ⟨s₂, fl, hcall, ⟨ws, m, -, hws, hk⟩ | ⟨rfl, hends⟩⟩
    · rw [htake] at hy
      exact .inl ⟨hpend, y, .inr hy, hb⟩
    · right
      rw [htake] at hcall
      refine ⟨fi, _, _, s₂, fl, hfi, hty, hcall, .inl ⟨ws, hws, ?_⟩⟩
      rw [hdrop] at hk
      exact stepsN_of_stuck (fun c' => Sim.Step.not_vals) (by simpa using hk)
    · right
      rw [htake] at hcall
      refine ⟨fi, _, _, s₂, .trap, hfi, hty, hcall, .inr ⟨rfl, ?_⟩⟩
      obtain ⟨oc, he', hst, hfr, hm⟩ := hends
      rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm
      rcases c with ⟨cs, cf, cc⟩
      dsimp only at he' hst hfr
      subst hst hfr
      have : cc = [.trap] := he'
      subst this
      rfl

/-- **The backward simulation of an invocation** (deterministic profile). -/
theorem back_invoke {o : GrowOracle} (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {n : Nat} {s : Store H} {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s)
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN (profile o) host n (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (profile o) host c c') :
    Pending host c.store c.code ∨
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow),
        s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        hostCall host s a vs (s₂, fl) ∧
        ((∃ ws, fl.retVals = some ws ∧ c = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
          (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) :=
  (back_invoke_core hT hH hs hS hok hrun hend).imp_left And.left

/-- **The backward simulation of an invocation, with reach evidence** (deterministic
profile): a stuck end is blocked at a host call `y` with no outcome, which is the
invoked function itself or a pending call of it (`PendO`), or ends as a native answer. -/
theorem back_invoke_reach {o : GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN (profile o) host n (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (profile o) host c c') :
    (∃ (y : (wasmOShape H).self.Op) (fi : FuncInst H) (hh : H),
        (y = ⟨a, (vs, s)⟩ ∨ PendO (hostCall host) ⟨a, (vs, s)⟩ y) ∧ y.2.2 = c.store ∧
        c.store.funcs[y.1]? = some fi ∧ fi.code = .host hh ∧ (∀ o, ¬ host hh c.store y.2.1 o) ∧
        AtCall c.store y.1 y.2.1 c.code) ∨
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow),
        s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        hostCall host s a vs (s₂, fl) ∧
        ((∃ ws, fl.retVals = some ws ∧ c = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
          (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) :=
  (back_invoke_core hT hH hs hS hok hrun hend).imp_left
    fun ⟨_, y, hy, fi, hh, h⟩ => ⟨y, fi, hh, hy, h⟩

end Silmaril.Proofs.Wasm.Abstract.HostEval
