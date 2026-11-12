module

public import Silmaril.Wasm.Models.FXPres.Defs
public import Silmaril.Wasm.Models.FXV.Thms

/-!
# `StepFXS` inside `StepFXR`, and the untyped `suspend` of `StepFXR`

* `stepFXS_incl`, `stepsFXS_incl`: every `StepFXS` step (run) is a `StepFXR` step (run); the
  typed rules only add the tag arity (`TagArity`).
* `tagArity_unique`: the arity is determined by the tag.
* **`stepR_suspend_ambiguous`** (refutation of a unique split under `StepFXR`): with one operand
  `v` before `suspend x`, `StepFXR` may pass `v` to the handler's label, or leave it in the
  captured context (`CtxV.seq [v] .hole []`); the two successors differ. `StepFXS` allows
  only the split with the tag's arity.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- `StepFXS ⊆ StepFXR`. -/
theorem stepFXS_incl {x y : ConfigFX H} (h : StepFXS P host fx x y) : StepFXR P host fx x y := by
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
  | contBind hk ha => exact .contBind hk ha
  | contBindNull ha => exact .contBindNull ha
  | contBindUsed hk ha => exact .contBindUsed hk ha
  | resume hk hr ha => exact .resume hk hr ha
  | resumeNull ha => exact .resumeNull ha
  | resumeUsed hk ha => exact .resumeUsed hk ha
  | resumeThrow hk ht hr _ => exact .resumeThrow hk ht hr
  | resumeThrowNull => exact .resumeThrowNull
  | suspend ht hE hc _ => exact .suspend ht hE hc
  | switch hk ht hE hc => exact .switch hk ht hE hc


theorem stepsFXS_incl {x y : ConfigFX H} (h : StepsFXS P host fx x y) :
    StepsFXR P host fx x y := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (stepFXS_incl hs)

theorem tagArity_unique {ti : TagInst} {n m : Nat} (hn : TagArity ti n) (hm : TagArity ti m) :
    n = m := by
  obtain ⟨tp, tr, h, rfl⟩ := hn
  obtain ⟨tp', tr', h', rfl⟩ := hm
  rw [h] at h'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h')
  rfl

/-- **Under `StepFXR` the split of `suspend` is not unique.** -/
theorem stepR_suspend_ambiguous {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {hs : List HClause} {v : FVal} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    StepFXR P host fx ⟨s, K, f, [.handler hs (fvals [v] ++ [.fx (.suspend x)])]⟩
        ⟨s, K ++ [some ⟨CtxV.hole.plug⟩], f,
          fvals [v] ++ [.contRef K.length, .core (.plain (.br l))]⟩ ∧
      StepFXR P host fx ⟨s, K, f, [.handler hs (fvals [v] ++ [.fx (.suspend x)])]⟩
        ⟨s, K ++ [some ⟨(CtxV.seq [v] .hole []).plug⟩], f,
          [.contRef K.length, .core (.plain (.br l))]⟩ ∧
      (fvals [v] ++ [.contRef K.length, .core (.plain (.br l))] : List AdminFX) ≠
        [.contRef K.length, .core (.plain (.br l))] := by
  have h₁ : StepFXR P host fx
      ⟨s, K, f, [.handler hs (CtxV.hole.plug (fvals [v] ++ [.fx (.suspend x)]))]⟩
      ⟨s, K ++ [some ⟨CtxV.hole.plug⟩], f,
        fvals [v] ++ [.contRef K.length, .core (.plain (.br l))]⟩ :=
    StepFXR.suspend (E := .hole) ht (fun h => h) hc
  have h₂ : StepFXR P host fx
      ⟨s, K, f, [.handler hs ((CtxV.seq [v] .hole []).plug (fvals [] ++ [.fx (.suspend x)]))]⟩
      ⟨s, K ++ [some ⟨(CtxV.seq [v] .hole []).plug⟩], f,
        fvals [] ++ [.contRef K.length, .core (.plain (.br l))]⟩ :=
    StepFXR.suspend (E := .seq [v] .hole []) ht (fun h => h) hc
  refine ⟨by simpa [CtxV.plug] using h₁, by simpa [CtxV.plug] using h₂, ?_⟩
  intro heq
  have := congrArg List.length heq
  simp [fvals] at this

end Silmaril.Proofs.Wasm.Models.FXPres
