module

public import Silmaril.Wasm.Models.FXV.Defs

/-!
# `StepFX` is included in `StepFX'`

Every rule of track H's `StepFX` is the instance of the corresponding `StepFX'` rule at Core
values (`fvals (liftV vs) = cvals vs`) and at the context `Ctx.toV E`
(`E.toV.plug = E.plug`). So:

* `stepFX_incl`: `StepFX ⊆ StepFX'`;
* `stepsFX_incl`, `infiniteTrace_incl`, **`behavioursFX_incl`**: runs, divergence and
  behaviours of `StepFX` are those of `StepFX'`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXV

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

@[simp] theorem fvals_liftV (vs : List Val) : fvals (liftV vs) = cvals vs := by
  simp only [fvals, liftV, cvals, vals, List.map_map]
  rfl

@[simp] theorem liftV_length (vs : List Val) : (liftV vs).length = vs.length := List.length_map _

@[simp] theorem liftV_eq_nil {vs : List Val} : liftV vs = [] ↔ vs = [] := List.map_eq_nil_iff

@[simp] theorem fvals_append (xs ys : List FVal) : fvals (xs ++ ys) = fvals xs ++ fvals ys :=
  List.map_append

@[simp] theorem fvals_nil : fvals [] = [] := rfl

@[simp] theorem fvals_cons (v : FVal) (vs : List FVal) :
    fvals (v :: vs) = v.toAdmin :: fvals vs := rfl

theorem liftV_ne {vs : List Val} {rest : List AdminFX} (h : vs ≠ [] ∨ rest ≠ []) :
    liftV vs ≠ [] ∨ rest ≠ [] := by
  simpa only [ne_eq, liftV_eq_nil] using h

theorem toV_plug_apply (E : Ctx) (c : List AdminFX) : E.toV.plug c = E.plug c := by
  induction E with
  | hole => rfl
  | seq vs E rest ih => simp only [Ctx.toV, CtxV.plug, Ctx.plug, fvals_liftV, ih]
  | label n k E ih => simp only [Ctx.toV, CtxV.plug, Ctx.plug, ih]
  | frame n f E ih => simp only [Ctx.toV, CtxV.plug, Ctx.plug, ih]
  | handler hs E ih => simp only [Ctx.toV, CtxV.plug, Ctx.plug, ih]

@[simp] theorem toV_plug (E : Ctx) : E.toV.plug = E.plug := funext (toV_plug_apply E)

@[simp] theorem toV_frameAt (E : Ctx) (f : Frame) : E.toV.frameAt f = E.frameAt f := by
  induction E generalizing f with
  | hole => rfl
  | seq vs E rest ih => exact ih f
  | label n k E ih => exact ih f
  | frame n fi E ih => exact ih fi
  | handler hs E ih => exact ih f

@[simp] theorem toV_handles (E : Ctx) (ta : Nat) : E.toV.Handles ta ↔ E.Handles ta := by
  induction E with
  | hole => rfl
  | seq vs E rest ih => exact ih
  | label n k E ih => exact ih
  | frame n fi E ih => exact ih
  | handler hs E ih => simp only [Ctx.toV, CtxV.Handles, Ctx.Handles, ih]

/-- The `suspend` rule at a context of `StepFX`. -/
theorem incl_suspend {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {E : Ctx} {vs : List Val} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    StepFX' P host fx ⟨s, K, f, [.handler hs (E.plug (cvals vs ++ [.fx (.suspend x)]))]⟩
      ⟨s, K ++ [some ⟨E.plug⟩], f, cvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩ := by
  have h' : StepFX' P host fx
      ⟨s, K, f, [.handler hs (E.toV.plug (fvals (liftV vs) ++ [.fx (.suspend x)]))]⟩
      ⟨s, K ++ [some ⟨E.toV.plug⟩], f,
        fvals (liftV vs) ++ [.contRef K.length, .core (.plain (.br l))]⟩ :=
    StepFX'.suspend (by rw [toV_frameAt]; exact ht) (by rw [toV_handles]; exact hE) hc
  simpa only [toV_plug, fvals_liftV] using h'

/-- The `switch` rule at a context of `StepFX`. -/
theorem incl_switch {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {E : Ctx} {vs : List Val} {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx} {ta : Nat}
    {ti : TagInst} (hk : K[k]? = some (some C))
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onSwitch ta)) :
    StepFX' P host fx
      ⟨s, K, f, [.handler hs (E.plug (cvals vs ++ [.contRef k, .fx (.switch ct x)]))]⟩
      ⟨s, K.set k none ++ [some ⟨E.plug⟩], f,
        [.handler hs (C.plug (cvals vs ++ [.contRef K.length]))]⟩ := by
  have h' : StepFX' P host fx
      ⟨s, K, f, [.handler hs (E.toV.plug (fvals (liftV vs) ++ [.contRef k, .fx (.switch ct x)]))]⟩
      ⟨s, K.set k none ++ [some ⟨E.toV.plug⟩], f,
        [.handler hs (C.plug (fvals (liftV vs) ++ [.contRef K.length]))]⟩ :=
    StepFX'.switch hk (by rw [toV_frameAt]; exact ht) (by rw [toV_handles]; exact hE) hc
  simpa only [toV_plug, fvals_liftV] using h'

/-- **`StepFX ⊆ StepFX'`.** -/
theorem stepFX_incl {x y : ConfigFX H} (h : StepFX P host fx x y) : StepFX' P host fx x y := by
  induction h with
  | core h => exact .core h
  | seq _ hne ih =>
    rw [← fvals_liftV]
    exact .seq ih (liftV_ne hne)
  | ctxLabel _ ih => exact .ctxLabel ih
  | ctxFrame _ ih => exact .ctxFrame ih
  | ctxHandler _ ih => exact .ctxHandler ih
  | block hbt hm =>
    simp only [← fvals_liftV]
    exact .block hbt (by simpa using hm)
  | loop hbt hm =>
    simp only [← fvals_liftV]
    exact .loop hbt (by simpa using hm)
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | labelVals => simp only [← fvals_liftV]; exact .labelVals
  | brLabelZero hl hn =>
    simp only [← fvals_liftV]
    exact .brLabelZero hl (by simpa using hn)
  | brLabelSucc hl => simp only [← fvals_liftV]; exact .brLabelSucc hl
  | brHandler => simp only [← fvals_liftV]; exact .brHandler
  | returnLabel => simp only [← fvals_liftV]; exact .returnLabel
  | returnHandler => simp only [← fvals_liftV]; exact .returnHandler
  | frameVals hn => simp only [← fvals_liftV]; exact .frameVals (by simpa using hn)
  | returnFrame hn => simp only [← fvals_liftV]; exact .returnFrame (by simpa using hn)
  | handlerVals => simp only [← fvals_liftV]; exact .handlerVals
  | trapSeq hne => simp only [← fvals_liftV]; exact .trapSeq (liftV_ne hne)
  | trapLabel => exact .trapLabel
  | trapFrame => exact .trapFrame
  | trapHandler => exact .trapHandler
  | throwSeq hne => simp only [← fvals_liftV]; exact .throwSeq (liftV_ne hne)
  | throwLabel => exact .throwLabel
  | throwFrame => exact .throwFrame
  | throwHandler => exact .throwHandler
  | invoke hc hf hcode hfx hn => exact .invoke hc hf hcode hfx hn
  | contNew hf => exact .contNew hf
  | contNewNull => exact .contNewNull
  | contBind hk => simp only [← fvals_liftV]; exact .contBind hk
  | contBindNull => simp only [← fvals_liftV]; exact .contBindNull
  | contBindUsed hk => simp only [← fvals_liftV]; exact .contBindUsed hk
  | resume hk hr => simp only [← fvals_liftV]; exact .resume hk hr
  | resumeNull => simp only [← fvals_liftV]; exact .resumeNull
  | resumeUsed hk => simp only [← fvals_liftV]; exact .resumeUsed hk
  | resumeThrow hk ht hr => exact .resumeThrow hk ht hr
  | resumeThrowNull => exact .resumeThrowNull
  | suspend ht hE hc => exact incl_suspend ht hE hc
  | switch hk ht hE hc => exact incl_switch hk ht hE hc

/-- Runs of `StepFX` are runs of `StepFX'`. -/
theorem stepsFX_incl {x y : ConfigFX H} (h : StepsFX P host fx x y) :
    StepsFX' P host fx x y := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (stepFX_incl hs)

/-- Divergence under `StepFX` is divergence under `StepFX'`. -/
theorem infiniteTrace_incl {x : ConfigFX H}
    (h : Silmaril.InfiniteTrace (StepFX P host fx) x) :
    Silmaril.InfiniteTrace (StepFX' P host fx) x :=
  Silmaril.InfiniteTrace.map id (fun _ _ => stepFX_incl) h

/-- **Every `StepFX` behaviour is a `StepFX'` behaviour.** -/
theorem behavioursFX_incl (x : ConfigFX H) :
    behavioursFX P host fx x ⊆ behavioursFX' P host fx x := by
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨d, r, stepsFX_incl hrun, hd, rfl⟩
  · exact Or.inr ⟨rfl, infiniteTrace_incl hdiv⟩

end Silmaril.Proofs.Wasm.Models.FXV
