module

public import Silmaril.Wasm.Models.FXPres.Defs
public import Silmaril.Wasm.Models.FXV.Defs

/-!
# The typed relation `StepFXS` is contained in the corrected relation `StepFX'`

`FXPres.stepFXS_incl` gives `StepFXS ⊆ StepFXR`, and `FXBindT.stepFXT_incl` gives
`StepFXT ⊆ StepFX'`; the middle inclusion `StepFXR ⊆ StepFXT` is proved only in that topic's
proof modules. Here the composite is proved directly, rule by rule:

* `stepFXS_sub_V`, `stepsFXS_sub_V`: every `StepFXS` step and run is a `StepFX'` step and run.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXContExit

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- **`StepFXS ⊆ StepFX'`.** -/
theorem stepFXS_sub_V {x y : ConfigFX H} (h : StepFXS P host fx x y) : StepFX' P host fx x y := by
  induction h with
  | core h => exact .core h
  | seq _ hne ih => exact .seq ih hne
  | ctxLabel _ ih => exact .ctxLabel ih
  | ctxFrame _ ih => exact .ctxFrame ih
  | ctxHandler _ ih => exact .ctxHandler ih
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | labelVals => exact .labelVals
  | brLabelZero hl hn => exact .brLabelZero hl hn
  | brLabelSucc hl => exact .brLabelSucc hl
  | brHandler => exact .brHandler
  | returnLabel => exact .returnLabel
  | returnHandler => exact .returnHandler
  | frameVals hn => exact .frameVals hn
  | returnFrame hn => exact .returnFrame hn
  | handlerVals => exact .handlerVals
  | dropCont => exact .dropCont
  | trapSeq hne => exact .trapSeq hne
  | trapLabel => exact .trapLabel
  | trapFrame => exact .trapFrame
  | trapHandler => exact .trapHandler
  | throwSeq hne => exact .throwSeq hne
  | throwLabel => exact .throwLabel
  | throwFrame => exact .throwFrame
  | throwHandler => exact .throwHandler
  | invoke hc hf hcode hfx hn => exact .invoke hc hf hcode hfx hn
  | contNew hf => exact .contNew hf
  | contNewNull => exact .contNewNull
  | contBind hk _ => exact .contBind hk
  | contBindNull _ => exact .contBindNull
  | contBindUsed hk _ => exact .contBindUsed hk
  | resume hk hr _ => exact .resume hk hr
  | resumeNull _ => exact .resumeNull
  | resumeUsed hk _ => exact .resumeUsed hk
  | resumeThrow hk ht hr _ => exact .resumeThrow hk ht hr
  | resumeThrowNull => exact .resumeThrowNull
  | suspend ht hE hc _ => exact .suspend ht hE hc
  | switch hk ht hE hc => exact .switch hk ht hE hc

/-- Runs of `StepFXS` are runs of `StepFX'`. -/
theorem stepsFXS_sub_V {x y : ConfigFX H} (h : StepsFXS P host fx x y) :
    StepsFX' P host fx x y := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (stepFXS_sub_V hs)

end Silmaril.Proofs.Wasm.Models.FXContExit
