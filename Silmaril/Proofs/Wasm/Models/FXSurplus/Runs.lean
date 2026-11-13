module

public import Silmaril.Wasm.Models.FXSurplus.Defs

/-!
# The `StepFX'` runs of the surplus program

Three finished runs of `surC`, at every profile, host and FX function table:

* `run_tight`: payload `[1]` (the tag's arity), `resume` without arguments: ends with `[1, 7]`;
* `run_arg`: payload `[1]`, but `resume` passes the `1` to the continuation: ends with `[7, 1]`;
* `run_surplus`: payload `[7, 1]`, so the continuation is the empty context and the branch drops
  `7`: ends with `[1]`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXSurplus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXSurplus
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- The continuation captured with payload `[1]`: `7` in front of the hole. -/
def kTight : ContFX := ⟨(CtxV.seq [.val (Val.i32 7)] .hole []).plug⟩

/-- The continuation captured with payload `[7, 1]`: the empty context. -/
def kSurplus : ContFX := ⟨CtxV.hole.plug⟩

/-- A step of the handler frame under the label, after the label's code `[c32 0]`. -/
theorem step_under {K K' : List (Option ContFX)} {es' : List AdminFX}
    (h : StepFX' P host fx ⟨surS H, K, surF, [surH]⟩ ⟨surS H, K', surF, es'⟩) :
    StepFX' P host fx ⟨surS H, K, surF, surCode⟩
      ⟨surS H, K', surF, [.label 2 surK (es' ++ [c32 0])]⟩ := by
  have h' := StepFX'.seq (vs := []) (rest := [c32 0]) h (Or.inr (by simp))
  exact StepFX'.ctxLabel h'

/-- `suspend` with the tag's payload `[1]`. -/
theorem sus_tight :
    StepFX' P host fx ⟨surS H, [], surF, [surH]⟩
      ⟨surS H, [some kTight], surF, [c32 1, .contRef 0, .core (.plain (.br l0))]⟩ :=
  StepFX'.suspend (E := .seq [.val (Val.i32 7)] .hole []) (vs := [.val (Val.i32 1)])
    (ti := ⟨tagTy⟩) rfl (by simp [CtxV.Handles]) rfl

/-- `suspend` with the longer payload `[7, 1]`. -/
theorem sus_surplus :
    StepFX' P host fx ⟨surS H, [], surF, [surH]⟩
      ⟨surS H, [some kSurplus], surF, [c32 7, c32 1, .contRef 0, .core (.plain (.br l0))]⟩ :=
  StepFX'.suspend (E := .hole) (vs := [.val (Val.i32 7), .val (Val.i32 1)])
    (ti := ⟨tagTy⟩) rfl (by simp [CtxV.Handles]) rfl

/-- The branch to the label, with `1` and the continuation. -/
theorem br_tight :
    StepFX' P host fx
      ⟨surS H, [some kTight], surF, [.label 2 surK ([c32 1, .contRef 0, .core (.plain (.br l0))] ++ [c32 0])]⟩
      ⟨surS H, [some kTight], surF, [c32 1, .contRef 0, .fx (.resume ct0 [])]⟩ :=
  StepFX'.brLabelZero (vs' := []) (vs := [.val (Val.i32 1), .cont 0]) (rest := [c32 0]) rfl rfl

/-- The branch to the label, dropping `7`. -/
theorem br_surplus :
    StepFX' P host fx
      ⟨surS H, [some kSurplus], surF,
        [.label 2 surK ([c32 7, c32 1, .contRef 0, .core (.plain (.br l0))] ++ [c32 0])]⟩
      ⟨surS H, [some kSurplus], surF, [c32 1, .contRef 0, .fx (.resume ct0 [])]⟩ :=
  StepFX'.brLabelZero (vs' := [.val (Val.i32 7)]) (vs := [.val (Val.i32 1), .cont 0])
    (rest := [c32 0]) rfl rfl

/-- `resume` without arguments, under the value `1`. -/
theorem resume_noarg {C : ContFX} :
    StepFX' P host fx ⟨surS H, [some C], surF, [c32 1, .contRef 0, .fx (.resume ct0 [])]⟩
      ⟨surS H, [none], surF, [c32 1, .handler [] (C.plug [])]⟩ := by
  have h := StepFX'.resume (P := P) (host := host) (fx := fx) (s := surS H) (K := [some C])
    (f := surF) (vs := []) (k := 0) (C := C) (ct := ct0) (hs := []) (hs' := []) rfl rfl
  exact StepFX'.seq (vs := [.val (Val.i32 1)]) (rest := []) h (Or.inl (by simp))

/-- `resume` passing `1` to the continuation. -/
theorem resume_arg {C : ContFX} :
    StepFX' P host fx ⟨surS H, [some C], surF, [c32 1, .contRef 0, .fx (.resume ct0 [])]⟩
      ⟨surS H, [none], surF, [.handler [] (C.plug [c32 1])]⟩ :=
  StepFX'.resume (vs := [.val (Val.i32 1)]) (k := 0) (C := C) (hs' := []) rfl rfl

/-- **The tight run**: ends with `[1, 7]`. -/
theorem run_tight :
    StepsFX' P host fx (surC H) (surEnd H [none] [c32 1, c32 7]) := by
  refine .tail (.tail (.tail (.single (step_under sus_tight)) br_tight) resume_noarg) ?_
  exact StepFX'.seq (vs := [.val (Val.i32 1)]) (rest := [])
    (StepFX'.handlerVals (vs := [.val (Val.i32 7)])) (Or.inl (by simp))

/-- **`resume` with an argument**: ends with `[7, 1]`. -/
theorem run_arg :
    StepsFX' P host fx (surC H) (surEnd H [none] [c32 7, c32 1]) := by
  refine .tail (.tail (.tail (.single (step_under sus_tight)) br_tight) resume_arg) ?_
  exact StepFX'.handlerVals (vs := [.val (Val.i32 7), .val (Val.i32 1)])

/-- **The surplus run**: ends with `[1]`. -/
theorem run_surplus :
    StepsFX' P host fx (surC H) (surEnd H [none] [c32 1]) := by
  refine .tail (.tail (.tail (.single (step_under sus_surplus)) br_surplus) resume_noarg) ?_
  exact StepFX'.seq (vs := [.val (Val.i32 1)]) (rest := []) (StepFX'.handlerVals (vs := []))
    (Or.inl (by simp))

end Silmaril.Proofs.Wasm.Models.FXSurplus
