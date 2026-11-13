module

public import Silmaril.Wasm.Component.FXExample.Defs
public import Silmaril.Wasm.Component.FXInv.Thms

/-!
# A module with an FX function: the run

Kernel evaluation of the instantiation of `exMod` (`prep_eq`, `exS_f0`, `exS_f1`, `alloc_eq`),
then the run of `run` on the FX engine, step by step:

1. the Core thread invoking `run` is a callout of the FX function (`stat_enter`, from the Core 3.0
   law `allocHost_callout`), so the engine enters it by `StepFX.invoke` (`step_enter`);
2. `ref.func 0` (a Core step), `cont.new` (a continuation of `g`), `resume` (a handler frame with no
   clauses around `g`'s call);
3. the Core call of `g` and its return (Core steps under the handler frame);
4. the handler frame, the label and the frame of `run` return `42` (`step_handler`, `step_label`,
   `step_frame`).

`run_ex`: the run, as `Steps (fxE P)`; `status_ex`: its final status is `returned [42]`
(`statusFX_vals`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXExample

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (StepFX AdminFX ContFX cvals)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Component.FXExample
open Silmaril.Wasm.Numerics (Profile)

/-! ## Kernel evaluation of the instantiation -/

theorem prep_eq : exPrep = some (exS, exI, none) := by rfl

theorem exS_f0 : exS.funcs[0]?.map (·.code) = some (.wasm ⟨⟨0⟩, [], [.intConst .i32 42]⟩) := by
  rfl

theorem exS_f0_type : (exS.funcs[0]?.map (·.type.expand?)) =
    some (some (.func .nil (.cons (.num (.int .i32)) .nil))) := by rfl

theorem exS_f1 : exS.funcs[1]?.map (·.code) = some (.host (.fx runF)) := by rfl

theorem alloc_eq :
    Silmaril.Wasm.SingleThreaded.allocHost exS₁ runDecl.type (FXCode.fx runF) = (exS, 1) := by
  rfl

theorem hI (P : Profile) : instOf (fxE P) exMod [] exIface = some ⟨exS, [(1 : Nat)]⟩ := by
  unfold instOf
  rw [show (fxE P).prepare? = prepareFX? from rfl]
  change (match exPrep with | some (s', inst, none) => _ | _ => none) = _
  rw [prep_eq]
  rfl

theorem hq (P : Profile) :
    callee? (E := fxE P) [(1 : Nat)] exIface (⟨0, by decide⟩, .flat []) = some ((1 : Nat), []) := by
  rfl

theorem f0 : ∃ fi, exS.funcs[0]? = some fi ∧ fi.code = .wasm ⟨⟨0⟩, [], [.intConst .i32 42]⟩ ∧
    Silmaril.Wasm.Validation.Expand fi.type (.func .nil (.cons (.num (.int .i32)) .nil)) := by
  rcases h : exS.funcs[0]? with _ | fi
  · exact absurd (congrArg (Option.map (·.code)) h) (by rw [exS_f0]; simp)
  · have hc : some fi.code = some (.wasm ⟨⟨0⟩, [], [.intConst .i32 42]⟩) := by
      simpa [h] using exS_f0
    have ht : some fi.type.expand? = some (some (.func .nil (.cons (.num (.int .i32)) .nil))) := by
      simpa [h] using exS_f0_type
    exact ⟨fi, rfl, Option.some.inj hc,
      Silmaril.Wasm.Validation.Expand.iff.mpr (Option.some.inj ht)⟩

theorem f1 : ∃ fi, exS.funcs[1]? = some fi ∧ fi.code = .host (.fx runF) := by
  rcases h : exS.funcs[1]? with _ | fi
  · exact absurd (congrArg (Option.map (·.code)) h) (by rw [exS_f1]; simp)
  · have hc : some fi.code = some (.host (.fx runF)) := by simpa [h] using exS_f1
    exact ⟨fi, rfl, Option.some.inj hc⟩

/-! ## Entering `run` -/

theorem mapM_toFlat_nil {args : List Execution.Core.Val}
    (h : args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some []) : args = [] := by
  cases args with
  | nil => rfl
  | cons a as =>
    rcases h1 : Silmaril.Wasm.SingleThreaded.toFlat? a <;>
      rcases h2 : List.mapM Silmaril.Wasm.SingleThreaded.toFlat? as <;> simp [h1, h2] at h

/-- A flat callout with no arguments is a callout with no arguments. -/
theorem flatStatus_callout_nil {H : Type} {st : Silmaril.Wasm.SingleThreaded.Status H} {h : H}
    (hc : Silmaril.Wasm.Component.Reference.flatStatus st = .callout h []) : st = .callout h [] := by
  cases st with
  | running => cases hc
  | returned r =>
    cases r <;> simp only [Silmaril.Wasm.Component.Reference.flatStatus] at hc <;>
      (try split at hc) <;> cases hc
  | stuck => cases hc
  | callout h' args =>
    simp only [Silmaril.Wasm.Component.Reference.flatStatus] at hc
    split at hc
    · rename_i hf
      cases hc
      rw [mapM_toFlat_nil hf]
    · cases hc

theorem stat_enter (P : Profile) :
    Silmaril.Wasm.Game.statusP P exS (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 1 []) =
      .callout (FXCode.fx runF) [] :=
  flatStatus_callout_nil
    ((core3P_lawful P).allocHost_callout (H := FXCode Nat) (args := []) alloc_eq rfl)

/-- The body of `run`, entered. -/
abbrev fr : Frame := Frame.forCall exI.core [] []

theorem step_enter (P : Profile) (fi : FuncInst (FXCode Nat)) (hf : exS.funcs[1]? = some fi)
    (hc : fi.code = .host (.fx runF)) :
    StepFX P (noHostFX Nat) fxOf
      (Silmaril.Wasm.Models.FX.ofCore
        ((Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 1 []).config exS))
      ⟨exS, [], {}, [.frame 1 fr [.label 1 []
        (runF.body.map Silmaril.Wasm.Models.FX.InstrFX.toAdmin)]]⟩ := by
  have h := StepFX.invoke (P := P) (host := noHostFX Nat) (fx := fxOf) (s := exS) (K := [])
    (f := {}) (vs := []) (c := .callRefType fi.type) trivial hf hc rfl rfl
  simpa [Silmaril.Wasm.Models.FX.ofCore, Silmaril.Wasm.SingleThreaded.Thread.config,
    Silmaril.Wasm.SingleThreaded.Thread.invokeFlat, Silmaril.Wasm.SingleThreaded.Thread.invoke,
    Execution.Core.invoke, hf, cvals, vals, FXDecl.func, runDecl] using h

/-! ## Stack switching and the call of `g` -/

section steps

variable (P : Profile) (fi : FuncInst (FXCode Nat))

/-- The continuation of `g`. -/
abbrev Cg : ContFX := ⟨fun c => c ++ [.core (.ref (.func 0)), .core (.callRefType fi.type)]⟩

/-- The frame of `g`. -/
abbrev fg : Frame := Frame.forCall fi.module [] []

theorem step_refFunc : StepFX P (noHostFX Nat) fxOf
    ⟨exS, [], {}, [.frame 1 fr [.label 1 []
      [.core (.plain (.refFunc ⟨0⟩)), .fx (.contNew ⟨0⟩), .fx (.resume ⟨0⟩ [])]]]⟩
    ⟨exS, [], {}, [.frame 1 fr [.label 1 []
      [.core (.ref (.func 0)), .fx (.contNew ⟨0⟩), .fx (.resume ⟨0⟩ [])]]]⟩ :=
  .ctxFrame (.ctxLabel (.seq (vs := []) (es := [.core (.plain (.refFunc ⟨0⟩))])
    (es' := [.core (.ref (.func 0))]) (rest := [.fx (.contNew ⟨0⟩), .fx (.resume ⟨0⟩ [])])
    (.core (cs := [.plain (.refFunc ⟨0⟩)]) (cs' := [.ref (.func 0)])
      (.reference (.refFunc (by rfl))))
    (Or.inr (by simp))))

theorem step_contNew (hf0 : exS.funcs[0]? = some fi) : StepFX P (noHostFX Nat) fxOf
    ⟨exS, [], {}, [.frame 1 fr [.label 1 []
      [.core (.ref (.func 0)), .fx (.contNew ⟨0⟩), .fx (.resume ⟨0⟩ [])]]]⟩
    ⟨exS, [some (Cg fi)], {}, [.frame 1 fr [.label 1 [] [.contRef 0, .fx (.resume ⟨0⟩ [])]]]⟩ :=
  .ctxFrame (.ctxLabel (.seq (vs := []) (es := [.core (.ref (.func 0)), .fx (.contNew ⟨0⟩)])
    (rest := [.fx (.resume ⟨0⟩ [])]) (.contNew hf0) (Or.inr (by simp))))

theorem step_resume : StepFX P (noHostFX Nat) fxOf
    ⟨exS, [some (Cg fi)], {}, [.frame 1 fr [.label 1 [] [.contRef 0, .fx (.resume ⟨0⟩ [])]]]⟩
    ⟨exS, [none], {}, [.frame 1 fr [.label 1 []
      [.handler [] [.core (.ref (.func 0)), .core (.callRefType fi.type)]]]]⟩ :=
  .ctxFrame (.ctxLabel (.resume (vs := []) (k := 0) (C := Cg fi) (hs := []) (hs' := []) rfl rfl))

theorem step_call (hf0 : exS.funcs[0]? = some fi)
    (hcode : fi.code = .wasm ⟨⟨0⟩, [], [.intConst .i32 42]⟩)
    (hexp : Silmaril.Wasm.Validation.Expand fi.type (.func .nil (.cons (.num (.int .i32)) .nil))) :
    StepFX P (noHostFX Nat) fxOf
      ⟨exS, [none], {}, [.frame 1 fr [.label 1 []
        [.handler [] [.core (.ref (.func 0)), .core (.callRefType fi.type)]]]]⟩
      ⟨exS, [none], {}, [.frame 1 fr [.label 1 []
        [.handler [] [.core (.frame 1 (fg fi) [.label 1 [] [.plain (.intConst .i32 42)]])]]]]⟩ :=
  .ctxFrame (.ctxLabel (.ctxHandler (.core (cs := [.ref (.func 0), .callRefType fi.type])
    (cs' := [.frame 1 (fg fi) [.label 1 [] [.plain (.intConst .i32 42)]]])
    (Step.callRefFunc (vs := []) (c := .callRefType fi.type) trivial hf0 hexp rfl hcode))))

theorem step_labelC : StepFX P (noHostFX Nat) fxOf
    ⟨exS, [none], {}, [.frame 1 fr [.label 1 []
      [.handler [] [.core (.frame 1 (fg fi) [.label 1 [] [.plain (.intConst .i32 42)]])]]]]⟩
    ⟨exS, [none], {}, [.frame 1 fr [.label 1 []
      [.handler [] [.core (.frame 1 (fg fi) [.plain (.intConst .i32 42)])]]]]⟩ :=
  .ctxFrame (.ctxLabel (.ctxHandler
    (.core (cs := [.frame 1 (fg fi) [.label 1 [] [.plain (.intConst .i32 42)]]])
      (cs' := [.frame 1 (fg fi) [.plain (.intConst .i32 42)]])
      (Step.ctxtFrame (Step.labelVals (vs := [v42]))))))

theorem step_frameC : StepFX P (noHostFX Nat) fxOf
    ⟨exS, [none], {}, [.frame 1 fr [.label 1 []
      [.handler [] [.core (.frame 1 (fg fi) [.plain (.intConst .i32 42)])]]]]⟩
    ⟨exS, [none], {}, [.frame 1 fr [.label 1 [] [.handler [] [.core (.plain (.intConst .i32 42))]]]]⟩ :=
  .ctxFrame (.ctxLabel (.ctxHandler (.core (cs := [.frame 1 (fg fi) [.plain (.intConst .i32 42)]])
    (cs' := [.plain (.intConst .i32 42)]) (Step.frameVals (vs := [v42]) rfl))))

end steps

/-! ## Returning -/

theorem step_handler (P : Profile) : StepFX P (noHostFX Nat) fxOf
    ⟨exS, [none], {}, [.frame 1 fr [.label 1 [] [.handler [] [.core (.plain (.intConst .i32 42))]]]]⟩
    ⟨exS, [none], {}, [.frame 1 fr [.label 1 [] [.core (.plain (.intConst .i32 42))]]]⟩ :=
  .ctxFrame (.ctxLabel (.handlerVals (vs := [v42])))

theorem step_label (P : Profile) : StepFX P (noHostFX Nat) fxOf
    ⟨exS, [none], {}, [.frame 1 fr [.label 1 [] [.core (.plain (.intConst .i32 42))]]]⟩
    ⟨exS, [none], {}, [.frame 1 fr [.core (.plain (.intConst .i32 42))]]⟩ :=
  .ctxFrame (.labelVals (vs := [v42]))

theorem step_frame (P : Profile) : StepFX P (noHostFX Nat) fxOf
    ⟨exS, [none], {}, [.frame 1 fr [.core (.plain (.intConst .i32 42))]]⟩
    ⟨exS, [none], {}, [.core (.plain (.intConst .i32 42))]⟩ :=
  .frameVals (vs := [v42]) rfl

/-! ## The run -/

theorem internal_of_step (P : Profile) {H : Type} {s s' : Store (FXCode H)}
    {K K' : List (Option ContFX)} {f f' : Frame} {c c' : List AdminFX}
    (h : StepFX P (noHostFX H) fxOf ⟨s, K, f, c⟩ ⟨s', K', f', c'⟩) :
    (fxE P).Internal (s, ThreadFX.fx K f c) (s', ThreadFX.fx K' f' c') :=
  Or.inl ⟨_, _, _, rfl, h⟩

theorem run_ex_of (P : Profile) {fi₁ fi : FuncInst (FXCode Nat)}
    (hf₁ : exS.funcs[1]? = some fi₁) (hc₁ : fi₁.code = .host (.fx runF))
    (hf0 : exS.funcs[0]? = some fi) (hcode : fi.code = .wasm ⟨⟨0⟩, [], [.intConst .i32 42]⟩)
    (hexp : Silmaril.Wasm.Validation.Expand fi.type (.func .nil (.cons (.num (.int .i32)) .nil))) :
    Silmaril.Wasm.Component.Engine.CoreEngine.Steps (fxE P) (exS, (fxE P).invoke (1 : Nat) [])
      (exS, ThreadFX.fx [none] {} (cvals [v42])) := by
  have e0 : InternalFX P (exS, ThreadFX.core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 1 []))
      (exS, ThreadFX.fx [] {} [.frame 1 fr [.label 1 []
        (runF.body.map Silmaril.Wasm.Models.FX.InstrFX.toAdmin)]]) :=
    Or.inr ⟨⟨runF, [], stat_enter P⟩, [], {}, _, rfl, step_enter P fi₁ hf₁ hc₁⟩
  exact .head e0 <| .head (internal_of_step P (step_refFunc P)) <|
    .head (internal_of_step P (step_contNew P fi hf0)) <|
    .head (internal_of_step P (step_resume P fi)) <|
    .head (internal_of_step P (step_call P fi hf0 hcode hexp)) <|
    .head (internal_of_step P (step_labelC P fi)) <|
    .head (internal_of_step P (step_frameC P fi)) <|
    .head (internal_of_step P (step_handler P)) <|
    .head (internal_of_step P (step_label P)) <|
    .single (internal_of_step P (step_frame P))

/-- **The run of `run`**: from the invocation to the FX thread at the value `42`. -/
theorem run_ex (P : Profile) :
    Silmaril.Wasm.Component.Engine.CoreEngine.Steps (fxE P) (exS, (fxE P).invoke (1 : Nat) [])
      (exS, ThreadFX.fx [none] {} (cvals [v42])) := by
  obtain ⟨fi₁, hf₁, hc₁⟩ := f1
  obtain ⟨fi, hf0, hcode, hexp⟩ := f0
  exact run_ex_of P hf₁ hc₁ hf0 hcode hexp

/-- **The final status**: returned `42`. -/
theorem status_ex (P : Profile) :
    (fxE P).status exS (ThreadFX.fx [none] {} (cvals [v42])) = .returned (.values [y42]) :=
  (Silmaril.Wasm.Component.FXInv.statusFX_vals P exS [none] {} [v42]).trans rfl

end Silmaril.Proofs.Wasm.Component.FXExample
