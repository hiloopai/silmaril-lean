module

public import Silmaril.Proofs.Wasm.Models.FXPresI.Prog
public import Silmaril.Wasm.Models.FXLower.Thms

/-!
# The `StepFX` continuation defect on typed configurations

`suspend_to_label_stuck` (`FXLower`) shows that `StepFX` cannot branch a continuation
reference out of a label. The defect is wider: no `StepFX` rule moves `ref.cont` out of a frame
or a handler frame either, and the configurations where this happens are typed by `TL`. On the
same configurations `StepFXS` steps (and `progressI` says it always does on `envP`):

* `frame_contRef_stuck`, `handler_contRef_stuck`: a frame, or a clause-free handler frame,
  around code whose first non-value is `ref.cont` not followed by an FX instruction does not
  step under `StepFX` (no host).
* `contExit_frame`, `contExit_handler`, `contExit_label`: a frame, a handler frame and a label
  returning one continuation; each is a `ConfigOk` configuration of `envP m₀`, it is stuck
  under `StepFX`, and it steps under `StepFXS` (`frame-vals`, `handler-vals`, `label-vals`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Models.FXPresI Silmaril.Proofs.Wasm.Models.FXPres Silmaril.Proofs.Wasm.Models.FXLower
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

theorem frame_body {n n' : Nat} {fi fi' : Frame} {B B' : List AdminFX}
    (h : [AdminFX.frame n' fi' B'] = [.frame n fi B]) : B' = B := by
  simp only [List.cons.injEq, AdminFX.frame.injEq, and_true] at h
  exact h.2.2

theorem handler_body {hs hs' : List HClause} {B B' : List AdminFX}
    (h : [AdminFX.handler hs' B'] = [.handler hs B]) : B' = B := by
  simp only [List.cons.injEq, AdminFX.handler.injEq, and_true] at h
  exact h.2

theorem handler_nil {hs : List HClause} {B B' : List AdminFX}
    (h : [AdminFX.handler hs B'] = [.handler [] B]) : hs = [] := by
  simp only [List.cons.injEq, AdminFX.handler.injEq, and_true] at h
  exact h.1

/-- **A frame around a stuck continuation reference is stuck** under `StepFX`. -/
theorem frame_contRef_stuck {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
    {W : List Val} {j : Nat} {T : List AdminFX} (hT : NoFXHead T) {y : ConfigFX H} :
    ¬ StepFX P noHost fx ⟨s, K, f, [.frame n fi (cvals W ++ .contRef j :: T)]⟩ y := by
  intro h
  generalize hx : (⟨s, K, f, [.frame n fi (cvals W ++ .contRef j :: T)]⟩ : ConfigFX H) = x at h
  have hc : x.code = [.frame n fi (cvals W ++ .contRef j :: T)] := by rw [← hx]
  cases h with
  | ctxFrame h' => exact contRef_stuck h' W j T hT (frame_body hc)
  | seq h' hne => exact no_step_nil h' (seq_single rfl hne hc)
  | frameVals | returnFrame | trapFrame | throwFrame =>
    exact absurd (congrArg fnvX (frame_body hc)) (by simp [cthrowing, throwing])
  | _ => fnvX_absurd hc

/-- **A clause-free handler frame around a stuck continuation reference is stuck** under
`StepFX`. -/
theorem handler_contRef_stuck {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {W : List Val} {j : Nat} {T : List AdminFX} (hT : NoFXHead T) {y : ConfigFX H} :
    ¬ StepFX P noHost fx ⟨s, K, f, [.handler [] (cvals W ++ .contRef j :: T)]⟩ y := by
  intro h
  generalize hx : (⟨s, K, f, [.handler [] (cvals W ++ .contRef j :: T)]⟩ : ConfigFX H) = x at h
  have hc : x.code = [.handler [] (cvals W ++ .contRef j :: T)] := by rw [← hx]
  cases h with
  | ctxHandler h' => exact contRef_stuck h' W j T hT (handler_body hc)
  | seq h' hne => exact no_step_nil h' (seq_single rfl hne hc)
  | handlerVals | brHandler | returnHandler | trapHandler | throwHandler =>
    exact absurd (congrArg fnvX (handler_body hc)) (by simp [cthrowing, throwing])
  | suspend _ _ hc' => simp [handler_nil hc] at hc'
  | switch _ _ _ hc' => simp [handler_nil hc] at hc'
  | _ => fnvX_absurd hc

/-! ## Typed witnesses -/

variable {m₀ : ModuleInst} {s : Store H} {f : Frame} {ct : TypeIdx}

theorem kOk_used : KOk (envP m₀) s [ct] [none] := by
  refine ⟨rfl, fun k ct' h => .inl ?_⟩
  cases k with
  | zero => rfl
  | succ k => simp at h

theorem tl_cont {Ls : List (List FTy)} {R : Option (List FTy)} :
    TL (envP m₀) s [ct] Ls R [.contRef 0] [] [.cont ct] :=
  TL.contRef (pre := []) (k := 0) rfl .nil

/-- A frame returning a continuation. -/
theorem contExit_frame {fi : Frame} (hf : f.module = m₀) (hm : fi.module = m₀) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, [.frame 1 fi [.contRef 0]]⟩ [.cont ct] ∧
      (∀ y, ¬ StepFX P noHost fx ⟨s, [none], f, [.frame 1 fi [.contRef 0]]⟩ y) ∧
      StepFXS P noHost fx ⟨s, [none], f, [.frame 1 fi [.contRef 0]]⟩
        ⟨s, [none], f, [.contRef 0]⟩ := by
  have ht : TL (envP m₀) s [ct] [] none [.frame 1 fi [.contRef 0]] [] [.cont ct] :=
    TL.frame (pre := []) hm rfl tl_cont .nil
  refine ⟨⟨hf, kOk_used, ht⟩, fun y => ?_, ?_⟩
  · exact frame_contRef_stuck (W := []) (T := []) (by simp [NoFXHead])
  · exact StepFXS.frameVals (vs := [.cont 0]) rfl

/-- A handler frame returning a continuation. -/
theorem contExit_handler (hf : f.module = m₀) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, [.handler [] [.contRef 0]]⟩ [.cont ct] ∧
      (∀ y, ¬ StepFX P noHost fx ⟨s, [none], f, [.handler [] [.contRef 0]]⟩ y) ∧
      StepFXS P noHost fx ⟨s, [none], f, [.handler [] [.contRef 0]]⟩
        ⟨s, [none], f, [.contRef 0]⟩ := by
  have ht : TL (envP m₀) s [ct] [] none [.handler [] [.contRef 0]] [] [.cont ct] :=
    TL.handler (pre := []) (by simp) tl_cont .nil
  refine ⟨⟨hf, kOk_used, ht⟩, fun y => ?_, ?_⟩
  · exact handler_contRef_stuck (W := []) (T := []) (by simp [NoFXHead])
  · exact StepFXS.handlerVals (vs := [.cont 0])

/-- A label returning a continuation. -/
theorem contExit_label (hf : f.module = m₀) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, [.label 1 [] [.contRef 0]]⟩ [.cont ct] ∧
      (∀ y, ¬ StepFX P noHost fx ⟨s, [none], f, [.label 1 [] [.contRef 0]]⟩ y) ∧
      StepFXS P noHost fx ⟨s, [none], f, [.label 1 [] [.contRef 0]]⟩
        ⟨s, [none], f, [.contRef 0]⟩ := by
  have ht : TL (envP m₀) s [ct] [] none [.label 1 [] [.contRef 0]] [] [.cont ct] :=
    TL.label (pre := []) (tl := [.cont ct]) rfl .nil tl_cont .nil
  refine ⟨⟨hf, kOk_used, ht⟩, fun y => ?_, ?_⟩
  · exact label_contRef_stuck (W := []) (T := []) (by simp [NoFXHead])
  · exact StepFXS.labelVals (vs := [.cont 0])

end Silmaril.Proofs.Wasm.Models.FXPresI
