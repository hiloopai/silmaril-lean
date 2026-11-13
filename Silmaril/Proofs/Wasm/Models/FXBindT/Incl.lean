module

public import Silmaril.Wasm.Models.FXBindT.Defs
public import Silmaril.Wasm.Models.FXVRuns.Thms

/-!
# `StepFXT` against `StepFX'`

`StepFXT` is `StepFX'` with typed `cont.bind` rules, so:

* `stepFXT_incl`, `stepsFXT_incl`, **`behavioursFXT_incl`**: every `StepFXT` step, run and
  behaviour is one of `StepFX'`;
* `stepFXT_of_noK`: on code without continuations (`NoKs`: no FX instruction, no continuation
  reference) every `StepFX'` step is a `StepFXT` step;
* **`behavioursFXT_noK`**: on such code `StepFXT`, `StepFX'` and (no FX functions) `StepFX`
  have the same behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXBindT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXBindT
open Silmaril.Proofs.Wasm.Models.FXVRuns (NoKs noKs_append noKs_label_body noKs_frame_body
  noKs_handler_body not_noK_site not_noK_switch step_noK behavioursFX'_noK)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- **`StepFXT ⊆ StepFX'`.** -/
theorem stepFXT_incl {x y : ConfigFX H} (h : StepFXT P host fx x y) : StepFX' P host fx x y := by
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
  | resume hk hr => exact .resume hk hr
  | resumeNull => exact .resumeNull
  | resumeUsed hk => exact .resumeUsed hk
  | resumeThrow hk ht hr => exact .resumeThrow hk ht hr
  | resumeThrowNull => exact .resumeThrowNull
  | suspend ht hE hc => exact .suspend ht hE hc
  | switch hk ht hE hc => exact .switch hk ht hE hc

/-- Runs of `StepFXT` are runs of `StepFX'`. -/
theorem stepsFXT_incl {x y : ConfigFX H} (h : StepsFXT P host fx x y) :
    StepsFX' P host fx x y := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (stepFXT_incl hs)

/-- **Every `StepFXT` behaviour is a `StepFX'` behaviour.** -/
theorem behavioursFXT_incl (x : ConfigFX H) :
    behavioursFXT P host fx x ⊆ behavioursFX' P host fx x := by
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨d, r, stepsFXT_incl hrun, hd, rfl⟩
  · exact Or.inr ⟨rfl, Silmaril.InfiniteTrace.map id (fun _ _ => stepFXT_incl) hdiv⟩

/-- The `ctxt-instrs` case of `stepFXT_of_noK`. -/
theorem noK_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {vs : List FVal} {es es' rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : NoKs es → StepFXT P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
    (hx : NoKs (fvals vs ++ es ++ rest)) :
    StepFXT P host fx ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  simp only [noKs_append] at hx
  exact .seq (ih hx.1.2) hne

/-- **On code without continuations, `StepFX'` steps are `StepFXT` steps.** -/
theorem stepFXT_of_noK {x y : ConfigFX H} (h : StepFX' P host fx x y) :
    NoKs x.code → StepFXT P host fx x y := by
  induction h with
  | core h => exact fun _ => .core h
  | seq _ hne ih => exact noK_seq hne ih
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

/-- `StepFX'` runs from code without continuations are `StepFXT` runs (no FX functions). -/
theorem stepsFXT_of_noK {x y : ConfigFX H} (h : StepsFX' P host noFX x y) (hx : NoKs x.code) :
    StepsFXT P host noFX x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hs _ ih => exact .head (stepFXT_of_noK hs hx) (ih (step_noK hs hx).2)

/-- Divergence from code without continuations (no FX functions). -/
theorem infiniteT_of_noK {x : ConfigFX H} (h : Silmaril.InfiniteTrace (StepFX' P host noFX) x)
    (hx : NoKs x.code) : Silmaril.InfiniteTrace (StepFXT P host noFX) x := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun y => NoKs y.code ∧ Silmaril.InfiniteTrace (StepFX' P host noFX) y) ?_ ⟨hx, h⟩
  rintro y ⟨hy, hdiv⟩
  obtain ⟨z, hz, hdiv'⟩ := Silmaril.InfiniteTrace.unfold hdiv
  exact ⟨z, stepFXT_of_noK hz hy, (step_noK hz hy).2, hdiv'⟩

/-- **On code without continuations `StepFXT` has the `StepFX` behaviours** (no FX
functions). -/
theorem behavioursFXT_noK {x : ConfigFX H} (hx : NoKs x.code) :
    behavioursFXT P host noFX x = behavioursFX P host noFX x := by
  rw [← behavioursFX'_noK hx]
  refine Set.Subset.antisymm (behavioursFXT_incl x) ?_
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨d, r, stepsFXT_of_noK hrun hx, hd, rfl⟩
  · exact Or.inr ⟨rfl, infiniteT_of_noK hdiv hx⟩

end Silmaril.Proofs.Wasm.Models.FXBindT
