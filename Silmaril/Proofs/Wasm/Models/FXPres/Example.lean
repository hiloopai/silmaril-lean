module

public import Silmaril.Proofs.Wasm.Models.FXPres.Suspend

/-!
# A typed configuration that steps

For any typing environment whose module has a type `$ct = [] → []`: the configuration with one
continuation (the identity context) and code `ref.cont 0; resume $ct` is typed
(`configOk_resume_id`) and takes a `StepFXS` step (`stepS_resume_id`). So `ConfigOk` is not
empty and the typed `resume` rule is reachable from it.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {E : TyEnv H} {P : Profile} {host : HostSemantics H}
  {fx : H → Option FuncFX}

/-- The identity continuation. -/
def idCont : ContFX := ⟨fun c => c⟩

theorem configOk_resume_id {s : Store H} {f : Frame} {ct : TypeIdx} (hf : f.module = E.m₀)
    (hct : contType? E.m₀ ct = some ([], [])) :
    ConfigOk E [ct] ⟨s, [some idCont], f, [.contRef 0, .fx (.resume ct [])]⟩ [] := by
  have hC : ContTy E s [ct] idCont ct := ⟨[], [], hct, fun _ _ _ _ _ hc => hc⟩
  refine ⟨hf, ⟨rfl, fun k ct' hk => ?_⟩, ?_⟩
  · cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact Or.inr ⟨idCont, rfl, hC⟩
    | succ k => simp at hk
  · have hr : TL E s [ct] [] none [.fx (.resume ct [])] ([] ++ E.tys [] ++ [.cont ct]) [] :=
      .resume (pre := []) hct (fun c hc => by simp at hc) (by simpa [TyEnv.tys] using TL.nil)
    exact .contRef (pre := []) rfl (by simpa [TyEnv.tys] using hr)

theorem stepS_resume_id {s : Store H} {f : Frame} {ct : TypeIdx}
    (hct : contType? f.module ct = some ([], [])) :
    StepFXS P host fx ⟨s, [some idCont], f, [.contRef 0, .fx (.resume ct [])]⟩
      ⟨s, [none], f, [.handler [] []]⟩ := by
  have ha : ResumeArity f.module ct ([] : List FVal).length := ⟨[], contParams_eq hct, rfl⟩
  have h := StepFXS.resume (P := P) (host := host) (fx := fx) (s := s)
    (K := [some idCont]) (f := f) (vs := []) (k := 0) (C := idCont) (hs := [])
    (hs' := []) rfl rfl ha
  simpa [idCont] using h

end Silmaril.Proofs.Wasm.Models.FXPres
