module

public import Silmaril.Wasm.LambdaRTL.Loop.Thms
public import Silmaril.Wasm.SSA.CoreCert.Thms

/-!
# Wasm Core 3.0 behaviours of a fragment function (loops included), through λRTL with loops

`behaviours_eq_evalObsL` composes `Silmaril.Wasm.SSA.behaviours_eq_run` with the exact theorems
of `Silmaril.Wasm.LambdaRTL.Loop.Thms`; its hypotheses are exactly those of `behaviours_eq_run`
(no `trFunc` side condition: every fragment function is translated). Core divergence
corresponds to a λRTL run that is stuck or divergent: `behaviours_eq_run` already identifies
Core divergence with the absence of a fragment run, which the fragment cannot split further.
-/

public section

namespace Silmaril.Wasm.LambdaRTL

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SSA

variable {H : Type}

/-- **Core 3.0 behaviours of a fragment function = its λRTL observations** (closed host, every
profile): returns and traps are the outcomes `o` with
`((trBodyL f).evalObs modelL (initStore f args)).run = Part.some (obsOfL o)`, and Core divergence
is a λRTL run that is stuck or divergent. -/
theorem behaviours_eq_evalObsL {s : Silmaril.Wasm.Execution.Core.Store H} {a : Nat}
    {fi : FuncInst H} {ft : FuncType} {bf : BFunc} {f : FragFunc} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm (coreFunc bf))
    (hty : Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (hf : ofBFunc? ft bf = some f) (hn : f.native = true)
    (hst : BExpr.structuredList bf.body = true) {vs : List Val}
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = f.params ∧
      behaviours P closedHost s a vs =
        {b | (∃ o, ((trBodyL f).evalObs modelL (initStore f args)).run = Part.some (obsOfL o) ∧
              b = outBeh (some o)) ∨
          (b = .diverges ∧
            (((trBodyL f).evalObs modelL (initStore f args)).run = Part.some (.error .stuck) ∨
              ((trBodyL f).evalObs modelL (initStore f args)).run = Part.none))} := by
  obtain ⟨args, hvs, hargs, hb⟩ := behaviours_eq_run hs hF hS hfi hcode hty hf hn hst hok P
  refine ⟨args, hvs, hargs, ?_⟩
  rw [hb]
  ext b
  simp only [Set.mem_ofPred_eq]
  have hσ := initStore_spec f args
  constructor
  · rintro (⟨o, hr, rfl⟩ | ⟨rfl, hno⟩)
    · exact Or.inl ⟨o, (trBodyL_run_iff hargs hσ o).1 hr, rfl⟩
    · exact Or.inr ⟨rfl, (trBodyL_noRun_iff hargs hσ).1 (fun ⟨o, ho⟩ => hno o ho)⟩
  · rintro (⟨o, he, rfl⟩ | ⟨rfl, hstk⟩)
    · exact Or.inl ⟨o, (trBodyL_run_iff hargs hσ o).2 he, rfl⟩
    · exact Or.inr ⟨rfl, fun o ho => (trBodyL_noRun_iff hargs hσ).2 hstk ⟨o, ho⟩⟩

end Silmaril.Wasm.LambdaRTL
