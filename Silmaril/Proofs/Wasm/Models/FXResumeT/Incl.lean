module

public import Silmaril.Wasm.Models.FXResume.Thms
public import Silmaril.Wasm.Models.FXBindT.Thms
public import Silmaril.Wasm.Models.FXResumeT.Defs

/-!
# `StepFXR` inside `StepFXT`, and on code without continuations

* `stepFXR_incl`, `stepsFXR_incl`, **`behavioursFXR_incl`**: every `StepFXR` step, run and
  behaviour is one of `StepFXT` (and so of `StepFX'`, `behavioursFXR_incl'`);
* `stepFXR_of_noK`: on code without continuations (`NoKs`) every `StepFX'` step is a
  `StepFXR` step;
* **`behavioursFXR_noK`**: on such code `StepFXR` and (no FX functions) `StepFX` have the
  same behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXResumeT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResumeT
open Silmaril.Proofs.Wasm.Models.FXVRuns (NoKs noKs_append noKs_label_body noKs_frame_body
  noKs_handler_body not_noK_site not_noK_switch step_noK behavioursFX'_noK)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- **`StepFXR ⊆ StepFXT`.** -/
theorem stepFXR_incl {x y : ConfigFX H} (h : StepFXR P host fx x y) : StepFXT P host fx x y := by
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
  | resume hk hr _ => exact .resume hk hr
  | resumeNull _ => exact .resumeNull
  | resumeUsed hk _ => exact .resumeUsed hk
  | resumeThrow hk ht hr => exact .resumeThrow hk ht hr
  | resumeThrowNull => exact .resumeThrowNull
  | suspend ht hE hc => exact .suspend ht hE hc
  | switch hk ht hE hc => exact .switch hk ht hE hc

/-- Runs of `StepFXR` are runs of `StepFXT`. -/
theorem stepsFXR_incl {x y : ConfigFX H} (h : StepsFXR P host fx x y) :
    StepsFXT P host fx x y := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (stepFXR_incl hs)

/-- **Every `StepFXR` behaviour is a `StepFXT` behaviour.** -/
theorem behavioursFXR_incl (x : ConfigFX H) :
    behavioursFXR P host fx x ⊆ behavioursFXT P host fx x := by
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨d, r, stepsFXR_incl hrun, hd, rfl⟩
  · exact Or.inr ⟨rfl, Silmaril.InfiniteTrace.map id (fun _ _ => stepFXR_incl) hdiv⟩

/-- Every `StepFXR` behaviour is a `StepFX'` behaviour. -/
theorem behavioursFXR_incl' (x : ConfigFX H) :
    behavioursFXR P host fx x ⊆ behavioursFX' P host fx x :=
  (behavioursFXR_incl x).trans (behavioursFXT_incl x)

/-- The `ctxt-instrs` case of `stepFXR_of_noK`. -/
theorem noK_seqR {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {vs : List FVal} {es es' rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : NoKs es → StepFXR P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
    (hx : NoKs (fvals vs ++ es ++ rest)) :
    StepFXR P host fx ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  simp only [noKs_append] at hx
  exact .seq (ih hx.1.2) hne

/-- **On code without continuations, `StepFX'` steps are `StepFXR` steps.** -/
theorem stepFXR_of_noK {x y : ConfigFX H} (h : StepFX' P host fx x y) :
    NoKs x.code → StepFXR P host fx x y := by
  induction h with
  | core h => exact fun _ => .core h
  | seq _ hne ih => exact noK_seqR hne ih
  | ctxLabel _ ih => exact fun hx => .ctxLabel (ih (noKs_label_body hx).2)
  | ctxFrame _ ih => exact fun hx => .ctxFrame (ih (noKs_frame_body hx))
  | ctxHandler _ ih => exact fun hx => .ctxHandler (ih (noKs_handler_body hx))
  | block hbt hm => exact fun _ => .block hbt hm
  | loop hbt hm => exact fun _ => .loop hbt hm
  | ifTrue hc => exact fun _ => .ifTrue hc
  | ifFalse => exact fun _ => .ifFalse
  | labelVals => exact fun _ => .labelVals
  | brLabelZero hl hn => exact fun _ => .brLabelZero hl hn
  | brLabelSucc hl => exact fun _ => .brLabelSucc hl
  | brHandler => exact fun _ => .brHandler
  | returnLabel => exact fun _ => .returnLabel
  | returnHandler => exact fun _ => .returnHandler
  | frameVals hn => exact fun _ => .frameVals hn
  | returnFrame hn => exact fun _ => .returnFrame hn
  | handlerVals => exact fun _ => .handlerVals
  | trapSeq hne => exact fun _ => .trapSeq hne
  | trapLabel => exact fun _ => .trapLabel
  | trapFrame => exact fun _ => .trapFrame
  | trapHandler => exact fun _ => .trapHandler
  | throwSeq hne => exact fun _ => .throwSeq hne
  | throwLabel => exact fun _ => .throwLabel
  | throwFrame => exact fun _ => .throwFrame
  | throwHandler => exact fun _ => .throwHandler
  | invoke hc hf hcode hfx hn => exact fun _ => .invoke hc hf hcode hfx hn
  | resumeThrow => exact fun hx => absurd hx (by simp [cvals])
  | resumeThrowNull => exact fun hx => absurd hx (by simp [cvals])
  | suspend => exact fun hx => (not_noK_site hx).elim
  | switch => exact fun hx => (not_noK_switch hx).elim
  | _ => exact fun hx => absurd hx (by simp)

/-- `StepFX'` runs from code without continuations are `StepFXR` runs (no FX functions). -/
theorem stepsFXR_of_noK {x y : ConfigFX H} (h : StepsFX' P host noFX x y) (hx : NoKs x.code) :
    StepsFXR P host noFX x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hs _ ih => exact .head (stepFXR_of_noK hs hx) (ih (step_noK hs hx).2)

/-- Divergence from code without continuations (no FX functions). -/
theorem infiniteR_of_noK {x : ConfigFX H} (h : Silmaril.InfiniteTrace (StepFX' P host noFX) x)
    (hx : NoKs x.code) : Silmaril.InfiniteTrace (StepFXR P host noFX) x := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun y => NoKs y.code ∧ Silmaril.InfiniteTrace (StepFX' P host noFX) y) ?_ ⟨hx, h⟩
  rintro y ⟨hy, hdiv⟩
  obtain ⟨z, hz, hdiv'⟩ := Silmaril.InfiniteTrace.unfold hdiv
  exact ⟨z, stepFXR_of_noK hz hy, (step_noK hz hy).2, hdiv'⟩

/-- **On code without continuations `StepFXR` has the `StepFX` behaviours** (no FX
functions). -/
theorem behavioursFXR_noK {x : ConfigFX H} (hx : NoKs x.code) :
    behavioursFXR P host noFX x = behavioursFX P host noFX x := by
  rw [← behavioursFX'_noK hx]
  refine Set.Subset.antisymm (behavioursFXR_incl' x) ?_
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨d, r, stepsFXR_of_noK hrun hx, hd, rfl⟩
  · exact Or.inr ⟨rfl, infiniteR_of_noK hdiv hx⟩

end Silmaril.Proofs.Wasm.Models.FXResumeT
