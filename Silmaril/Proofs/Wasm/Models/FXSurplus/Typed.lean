module

public import Silmaril.Proofs.Wasm.Models.FXSurplus.Runs

/-!
# The surplus program is typed, and its typed run

* `surC_ok`: `surC` is a typed configuration of `FXPresI.envP surM` at `[i32, i32]`, with no
  continuation slots;
* `run_typed`: the tight run is a `StepFXS` run (the payload has the tag's arity, `resume` the
  continuation type's);
* `end_one_not_ok`: the end `[1]` of the surplus run is not typed at `[i32, i32]`, for any slot
  typing.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXSurplus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXSurplus Silmaril.Wasm.Models.FXResumeT
open Silmaril.Wasm.Models.FXPres Silmaril.Wasm.Models.FXPresI
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- `i32` as an FX type. -/
abbrev fi32 : FTy := .val ti32

/-- `i32.const n` has type `[] → [i32]` after any stack. -/
theorem tl_const {Ls : List (List FTy)} {R : Option (List FTy)} {n : BitVec 32}
    {as : List AdminFX} {pre t : List FTy}
    (hr : TL (envP surM) (surS H) [] Ls R as (pre ++ [fi32]) t) :
    TL (envP surM) (surS H) [] Ls R (c32 n :: as) pre t := by
  have h := TL.core (E := envP surM) (s := surS H) (Γ := []) (Ls := Ls) (R := R)
    (a := .plain (.intConst .i32 n)) (pre := pre) (i₀ := []) (o₀ := [intTy .i32])
    (CtI.intConst) (by simp [IsCtl]) hr
  simpa [c32] using h

/-- The handler's body: `[] → [i32]`. -/
theorem tl_body :
    TL (envP surM) (surS H) [] [] none [c32 7, c32 1, .fx (.suspend x0)] [] [fi32] := by
  refine tl_const (pre := []) (tl_const (pre := [fi32]) ?_)
  have h := TL.suspend (E := envP surM) (s := surS H) (Γ := []) (Ls := []) (R := none)
    (x := x0) (tp := [ti32]) (tr := []) (ta := 0) (ti := ⟨tagTy⟩) (as := [])
    (pre := [fi32]) (t := [fi32]) rfl rfl rfl (by simpa [TyEnv.tys] using TL.nil)
  simpa [TyEnv.tys, envP, envI] using h

/-- The label's code `resume $ct`: `[i32, (ref $ct)] → [i32, i32]`. -/
theorem tl_k :
    TL (envP surM) (surS H) [] [] none (surK.map InstrFX.toAdmin) [fi32, .cont ct0]
      [fi32, fi32] := by
  have h := TL.resume (E := envP surM) (s := surS H) (Γ := []) (Ls := []) (R := none)
    (ct := ct0) (hs := []) (ps := []) (rs := [ti32]) (as := []) (pre := [fi32])
    (t := [fi32, fi32]) rfl (by simp) (by simpa [TyEnv.tys, envP, envI] using TL.nil)
  simpa [TyEnv.tys, envP, envI, surK, InstrFX.toAdmin] using h

/-- The clause `(on $t $on)` fits the label `[i32, (ref $ct)]` and the handler's `[i32]`. -/
theorem clause_ok :
    ∀ c ∈ surHs, HClauseOk (envP surM) (surS H) [[fi32, .cont ct0]] [fi32] c := by
  intro c hc
  simp only [surHs, List.mem_singleton] at hc
  subst hc
  exact ⟨⟨tagTy⟩, [ti32], [], ct0, [ti32], rfl, rfl, rfl, rfl, rfl⟩

/-- The label's body: `[] → [i32, i32]` under the label `[i32, (ref $ct)]`. -/
theorem tl_lbody :
    TL (envP surM) (surS H) [] [[fi32, .cont ct0]] none [surH, c32 0] [] [fi32, fi32] := by
  refine TL.handler (ts := [fi32]) (pre := []) clause_ok tl_body ?_
  exact tl_const (pre := [fi32]) TL.nil

/-- **The surplus program is typed** at `[i32, i32]`. -/
theorem surC_ok : ConfigOk (envP surM) [] (surC H) [fi32, fi32] := by
  refine ⟨rfl, ⟨rfl, fun k ct h => by simp at h⟩, ?_⟩
  exact TL.label (tl := [fi32, .cont ct0]) (te := [fi32, fi32]) (pre := []) rfl tl_k tl_lbody
    TL.nil

/-- **The tight run is typed**: a `StepFXS` run to `[1, 7]`. -/
theorem run_typed : StepsFXS P host fx (surC H) (surEnd H [none] [c32 1, c32 7]) := by
  have h₁ : StepFXS P host fx ⟨surS H, [], surF, [surH]⟩
      ⟨surS H, [some kTight], surF, [c32 1, .contRef 0, .core (.plain (.br l0))]⟩ :=
    StepFXS.suspend (E := .seq [.val (Val.i32 7)] .hole []) (vs := [.val (Val.i32 1)])
      (ti := ⟨tagTy⟩) rfl (by simp [CtxV.Handles]) rfl ⟨[ti32], [], rfl, rfl⟩
  have h₁' := StepFXS.ctxLabel (n := 2) (k := surK)
    (StepFXS.seq (vs := []) (rest := [c32 0]) h₁ (Or.inr (by simp)))
  have h₂ : StepFXS P host fx
      ⟨surS H, [some kTight], surF,
        [.label 2 surK ([c32 1, .contRef 0, .core (.plain (.br l0))] ++ [c32 0])]⟩
      ⟨surS H, [some kTight], surF, [c32 1, .contRef 0, .fx (.resume ct0 [])]⟩ :=
    StepFXS.brLabelZero (vs' := []) (vs := [.val (Val.i32 1), .cont 0]) (rest := [c32 0]) rfl rfl
  have h₃ : StepFXS P host fx
      ⟨surS H, [some kTight], surF, [c32 1, .contRef 0, .fx (.resume ct0 [])]⟩
      ⟨surS H, [none], surF, [c32 1, .handler [] (kTight.plug [])]⟩ := by
    have h := StepFXS.resume (P := P) (host := host) (fx := fx) (s := surS H)
      (K := [some kTight]) (f := surF) (vs := []) (k := 0) (C := kTight) (ct := ct0) (hs := [])
      (hs' := []) rfl rfl ⟨[], rfl, rfl⟩
    exact StepFXS.seq (vs := [.val (Val.i32 1)]) (rest := []) h (Or.inl (by simp))
  have h₄ : StepFXS P host fx ⟨surS H, [none], surF, [c32 1, .handler [] (kTight.plug [])]⟩
      (surEnd H [none] [c32 1, c32 7]) :=
    StepFXS.seq (vs := [.val (Val.i32 1)]) (rest := [])
      (StepFXS.handlerVals (vs := [.val (Val.i32 7)])) (Or.inl (by simp))
  exact .tail (.tail (.tail (.single h₁') h₂) h₃) h₄

/-- **One value is not typed at two.** -/
theorem tl_one_not {s : Store H} {Γ : List TypeIdx} {n : BitVec 32} {a b : FTy} :
    ¬ TL (envP surM) s Γ [] none [c32 n] [] [a, b] := by
  intro h
  generalize hi : ([] : List FTy) = i at h
  generalize ho : [a, b] = o at h
  cases h with
  | core hc hn hr =>
    cases hc
    generalize hm : (_ ++ [intTy IntType.i32] : List FTy) = m at hr
    cases hr
    subst ho
    have hl := congrArg List.length hm
    have hl' := congrArg List.length hi
    simp at hl hl'

/-- **The end of the surplus run is not typed at `[i32, i32]`.** -/
theorem end_one_not_ok {Γ : List TypeIdx} {K : List (Option ContFX)} {n : BitVec 32} {a b : FTy} :
    ¬ ConfigOk (envP surM) Γ (surEnd H K [c32 n]) [a, b] :=
  fun h => tl_one_not h.2.2

end Silmaril.Proofs.Wasm.Models.FXSurplus
