module

public import Silmaril.Proofs.Wasm.Interp.Total

@[expose] public section

/-!
# `DivSim` for typed invocations of native, arity-checked stores (proofs)

`divSim_det`: if the native interpreter runs out of fuel at every fuel, Core diverges: otherwise
the invocation has no infinite host-free trace, so (`term_of_acc`) the callee body has a native
evaluation, which the fuel interpreter reaches (`run_of_eval`) with a result `invokeRun`
reports. `divSim_native`: at every profile, by profile independence. New proofs. Summary in
`Silmaril.Wasm.Interp.Thms`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Execution.Core.Sim

variable {H : Type} {s : Store H} {a : Nat} {vs : List Val}

/-- The native function type of a Core function type. -/
theorem funcType_of_expand {d : Validation.DefType} {ps rs : Validation.Ty (.list .val)}
    (he : Validation.Expand d (.func ps rs)) :
    Validation.DefType.funcType? d = some (ps.toList, rs.toList) := by
  unfold Validation.DefType.funcType?
  rw [Validation.Expand.iff.mp he]

/-- A terminating callee body makes `invokeRun` report a result. -/
theorem invokeRun_some {fuel : Nat} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    {s' : Store H} {F' : Frame} {flb : Binaryen.Flow} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hrun : Binaryen.run fuel s (Frame.forCall fi.module vs fn.locals) []
      (Binaryen.liftInstrs fn.body) = some (s', F', flb))
    (hflb : (∃ ws, flb.retVals = some ws) ∨ flb = .trap ∨ ∃ t, flb = .throw t) :
    Binaryen.invokeRun fuel s a vs ≠ none := by
  unfold Binaryen.invokeRun
  rw [hfi]
  simp only [hcode, hty, hrun]
  rcases hflb with ⟨ws, hws⟩ | rfl | ⟨t, rfl⟩
  · rcases flb with _ | ⟨_ | _, _⟩ | _ | _ | _ <;> simp_all [Binaryen.Flow.retVals]
  · simp
  · simp

/-- The callee body of an invocation, in its label and frame. -/
theorem invoke_body_cfg {fi : FuncInst H} {fn : Func} (n : Nat) :
    (⟨s, {}, [.frame n (Frame.forCall fi.module vs fn.locals)
        [.label n [] (expression fn.body)]]⟩ : Config H) =
      (mapFrame [] n {} [] ∘ mapLabel [] n [] [])
        (pcfg s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body)) := by
  simp [mapFrame, mapLabel, pcfg, vals, Binaryen.lowerList_liftInstrs]

/-- **`DivSim`** at every deterministic profile, for typed invocations of native, checked
stores. -/
theorem divSim_det {o : GrowOracle} (hs : StoreOk s) (hF : Binaryen.NativeFuncsOk s.funcs)
    (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) : Binaryen.DivSim (profile o) s a vs := by
  intro hnone
  by_contra hnd
  have hacc : Acc (fun X K => Desc o K X) (invoke s a vs) := acc_desc hnd
  obtain ⟨-, -, rts, -, -, hc⟩ := invoke_ok hs hok
  obtain ⟨fi, ps', rs', hfi, he, hvt⟩ := hok
  obtain ⟨fn, hcode, -⟩ := hF fi (List.mem_of_getElem? hfi)
  have hty := funcType_of_expand he
  have hlen : vs.length = ps'.toList.length := args_length ⟨fi, ps', rs', hfi, he, hvt⟩ hfi hty
  have enter := steps_invoke_enter (P := profile o) (host := Det.noHost) hfi hcode hty hlen
  rw [invoke_body_cfg] at enter
  have hg : SP o (mapFrame (H := H) [] rs'.toList.length {} [] ∘ mapLabel [] rs'.toList.length [] []) :=
    SP.comp (sp_frame _ _ _ _) (sp_label _ _ _ _)
  have hct : ContextTyped
      (pcfg s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body)) :=
    ContextTyped.label (ContextTyped.frame (ContextTyped.steps (ContextTyped.of_configOk hc) enter))
  obtain ⟨ob, hb, hob⟩ := endsAt_eq (hS a fi fn _ _ hfi hcode hty)
  have hbc : chk s.funcs (Frame.forCall fi.module vs fn.locals).module
      (Frame.forCall fi.module vs fn.locals).locals.length rs'.toList.length [rs'.toList.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
    rw [forCall_length _ _ hlen]
    exact hb
  obtain ⟨r, hev⟩ := term_of_acc hacc _ s _ [] _ _ hg rfl enter _ _ _ hbc hct hF hS
  obtain ⟨hokb, -⟩ := flowOk_of_eval hev hS hbc
  obtain ⟨fuel, hrun⟩ := Binaryen.run_of_eval hev
  rcases r with ⟨s', F', flb⟩
  exact invokeRun_some hfi hcode hty hrun (callee_flow hokb) (hnone fuel)

/-- **`DivSim` at every profile** for typed invocations of native, checked stores. -/
theorem divSim_native {P : Profile} (hs : StoreOk s) (hF : Binaryen.NativeFuncsOk s.funcs)
    (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) : Binaryen.DivSim P s a vs :=
  (divSim_profile_iff hF).mp (divSim_det (o := fun _ _ _ _ => false) hs hF hS hok)

/-- **Native behaviours are Core behaviours at every profile** on typed invocations of native,
arity-checked stores. -/
theorem behaviours_eq_nbeh_native {P : Profile} (hs : StoreOk s)
    (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) :
    behaviours P Binaryen.closedHost s a vs = Binaryen.nbeh s a vs :=
  behaviours_eq_nbeh_of_divSim (P' := P) hs hF hS hok (divSim_native hs hF hS hok)

end Silmaril.Wasm.Interp
