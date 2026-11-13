module

public import Silmaril.Wasm.LambdaRTL.Thms
public import Silmaril.Wasm.SSA.CoreCert.Thms

/-!
# Wasm Core 3.0 behaviours of a loop-free fragment function, through λRTL

`behaviours_eq_evalObs` composes `Silmaril.Wasm.SSA.behaviours_eq_run` (the Core 3.0 behaviours of
a typed invocation of a function whose code is that of a recognised, arity-checked, structured
fragment function `f`, closed host, every profile) with the exact simulation of
`Silmaril.Wasm.LambdaRTL.Thms`: when `f` has no `loop` (`trFunc f = some R`), those behaviours are
read off the λRTL run of `R` from `initStore f args`. Its hypotheses are exactly those of
`behaviours_eq_run` plus `trFunc f = some R`; no hypothesis is added or dropped.
-/

public section

namespace Silmaril.Wasm.LambdaRTL

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SSA

variable {H : Type}

/-- **Core 3.0 behaviours of a loop-free fragment function = its λRTL observations**: returns
and traps are the outcomes `o` with `R.evalObs model (initStore f args) = obsOf o`, and Core
divergence is exactly a stuck λRTL run, at every profile, under the closed host. -/
theorem behaviours_eq_evalObs {s : Silmaril.Wasm.Execution.Core.Store H} {a : Nat}
    {fi : FuncInst H} {ft : FuncType} {bf : BFunc} {f : FragFunc} {R : WRegion}
    (hs : StoreOk s) (hF : NativeFuncsOk s.funcs)
    (hS : Silmaril.Wasm.Interp.StoreChk s.funcs) (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm (coreFunc bf))
    (hty : Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (hf : ofBFunc? ft bf = some f) (hn : f.native = true)
    (hst : BExpr.structuredList bf.body = true) (hR : trFunc f = some R) {vs : List Val}
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = f.params ∧
      behaviours P closedHost s a vs =
        {b | (∃ o, R.evalObs model (initStore f args) = obsOf o ∧ b = outBeh (some o)) ∨
          (b = .diverges ∧ R.evalObs model (initStore f args) = .error .stuck)} := by
  obtain ⟨args, hvs, hargs, hb⟩ := behaviours_eq_run hs hF hS hfi hcode hty hf hn hst hok P
  refine ⟨args, hvs, hargs, ?_⟩
  rw [hb]
  ext b
  simp only [Set.mem_ofPred_eq]
  have hσ := initStore_spec f args
  constructor
  · rintro (⟨o, hr, rfl⟩ | ⟨rfl, hno⟩)
    · exact Or.inl ⟨o, (trFunc_run_iff hR hargs hσ o).1 hr, rfl⟩
    · exact Or.inr ⟨rfl, (trFunc_stuck_iff hR hargs hσ).1 (fun ⟨o, ho⟩ => hno o ho)⟩
  · rintro (⟨o, he, rfl⟩ | ⟨rfl, hstk⟩)
    · exact Or.inl ⟨o, (trFunc_run_iff hR hargs hσ o).2 he, rfl⟩
    · exact Or.inr ⟨rfl, fun o ho => (trFunc_stuck_iff hR hargs hσ).2 hstk ⟨o, ho⟩⟩

end Silmaril.Wasm.LambdaRTL
