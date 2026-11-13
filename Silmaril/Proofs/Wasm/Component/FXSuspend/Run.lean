module

public import Silmaril.Proofs.Wasm.Component.FXSuspend.Inst

/-!
# A module whose code suspends: the run

The run of `run` on the engine with suspension `fxEV P`, step by step (each a `StepFX'` step):

1. the Core thread invoking `run` is a callout of the FX function (`stat_enter`, the Core 3.0
   law `allocHost_callout`), so the engine enters it (`step_enter`);
2. `block` (`step_block`), `ref.func 0` (`step_refFunc`: function index 0 is `sus`, an FX
   function, through `fxInst`), `cont.new` (`step_contNew`), `resume` with clause `(on 0 0)`
   (`step_resume`: a handler frame around the call of `sus`), entering `sus` under the handler
   (`step_invoke`);
3. **`suspend 0`** (`step_suspend`): the context from the handler to the `suspend` (the frame and
   label of `sus`, and the rest `i32.const 7` of its body) becomes continuation 1, and the
   handler is replaced by `contRef 1; br 0`;
4. **the branch carries the continuation out of the block** (`step_br`, `StepFX'.brLabelZero`
   with an FX value; in `StepFX` this configuration is stuck);
5. `resume 0` of continuation 1 with no handler clauses (`step_resume₂`) reinstates the
   frame and label of `sus` at `i32.const 7`;
6. the label, frame and handler around `7`, then the label and frame of `run` return it.

`run_ex`: the run, as `Steps (fxEV P)`; `status_ex`: its final status is `returned [7]`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXSuspend

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (AdminFX ContFX HClause cvals)
open Silmaril.Wasm.Models.FXV (StepFX' CtxV FVal fvals)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.FXEngine
  Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Component.FXSuspend
open Silmaril.Wasm.Numerics (Profile)

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

/-- The frame of `run` and of `sus`. -/
abbrev fr : Frame := Frame.forCall exI' [] []

/-- The code `i32.const 7`. -/
abbrev c7 : AdminFX := .core (.plain (.intConst .i32 7))

/-- The rest of `run`'s body after the block. -/
abbrev R : List AdminFX := [.fx (.resume ⟨0⟩ [])]

/-- The handler clause `(on 0 0)`, resolved. -/
abbrev hs : List HClause := [.onLabel 0 ⟨0⟩]

/-- The context captured by `suspend`: the frame and label of `sus`, before `i32.const 7`. -/
abbrev Es : CtxV := .frame 1 fr (.label 1 [] (.seq [] .hole [c7]))

/-- Run's frame and label around `c`. -/
abbrev wrap (c : List AdminFX) : List AdminFX := [.frame 1 fr [.label 1 [] c]]

/-- A step of `run`'s body. -/
abbrev SB (P : Profile) (K : List (Option ContFX)) (c : List AdminFX)
    (K' : List (Option ContFX)) (c' : List AdminFX) : Prop :=
  StepFX' P (noHostFX Nat) fxOf ⟨exS, K, fr, c⟩ ⟨exS, K', fr, c'⟩

theorem lift (P : Profile) {K K' : List (Option ContFX)} {c c' : List AdminFX}
    (h : SB P K c K' c') :
    StepFX' P (noHostFX Nat) fxOf ⟨exS, K, {}, wrap c⟩ ⟨exS, K', {}, wrap c'⟩ :=
  .ctxFrame (.ctxLabel h)

theorem step_enter (P : Profile) (fi : FuncInst (FXCode Nat)) (hf : exS.funcs[1]? = some fi)
    (hc : fi.code = .host (.fx runF)) :
    StepFX' P (noHostFX Nat) fxOf
      (Silmaril.Wasm.Models.FX.ofCore
        ((Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 1 []).config exS))
      ⟨exS, [], {}, wrap (runF.body.map Silmaril.Wasm.Models.FX.InstrFX.toAdmin)⟩ := by
  have h := StepFX'.invoke (P := P) (host := noHostFX Nat) (fx := fxOf) (s := exS) (K := [])
    (f := {}) (vs := []) (c := .callRefType fi.type) trivial hf hc rfl rfl
  simpa [Silmaril.Wasm.Models.FX.ofCore, Silmaril.Wasm.SingleThreaded.Thread.config,
    Silmaril.Wasm.SingleThreaded.Thread.invokeFlat, Silmaril.Wasm.SingleThreaded.Thread.invoke,
    Execution.Core.invoke, hf, cvals, vals, FXDecl.func, runDecl] using h

/-! ## The block, the continuation of `sus`, and the handler -/

section steps

variable (P : Profile) (fi : FuncInst (FXCode Nat))

theorem step_block : SB P []
    [.block (.value (.num (.int .i32))) blockBody, .fx (.resume ⟨0⟩ [])] []
    ([.label 1 [] (blockBody.map Silmaril.Wasm.Models.FX.InstrFX.toAdmin)] ++ R) :=
  .seq (vs := []) (es := [.block (.value (.num (.int .i32))) blockBody]) (rest := R)
    (StepFX'.block (vs := []) (t₁ := []) (t₂ := [.num (.int .i32)]) (by rfl) rfl)
    (Or.inr (by simp))

theorem step_refFunc : SB P []
    ([.label 1 [] [.core (.plain (.refFunc ⟨0⟩)), .fx (.contNew ⟨0⟩),
      .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]), .core (.plain .unreachable)]] ++ R) []
    ([.label 1 [] [.core (.ref (.func 0)), .fx (.contNew ⟨0⟩),
      .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]), .core (.plain .unreachable)]] ++ R) :=
  .seq (vs := []) (rest := R) (.ctxLabel (.seq (vs := [])
    (es := [.core (.plain (.refFunc ⟨0⟩))]) (es' := [.core (.ref (.func 0))])
    (rest := [.fx (.contNew ⟨0⟩), .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]), .core (.plain .unreachable)])
    (.core (cs := [.plain (.refFunc ⟨0⟩)]) (cs' := [.ref (.func 0)])
      (.reference (.refFunc (by rfl))))
    (Or.inr (by simp)))) (Or.inr (by simp))

/-- The continuation of `sus`. -/
abbrev C0 : ContFX := ⟨fun c => c ++ [.core (.ref (.func 0)), .core (.callRefType fi.type)]⟩

theorem step_contNew (hf0 : exS.funcs[0]? = some fi) : SB P []
    ([.label 1 [] [.core (.ref (.func 0)), .fx (.contNew ⟨0⟩),
      .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]), .core (.plain .unreachable)]] ++ R) [some (C0 fi)]
    ([.label 1 [] [.contRef 0, .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]),
      .core (.plain .unreachable)]] ++ R) :=
  .seq (vs := []) (rest := R) (.ctxLabel (.seq (vs := [])
    (es := [.core (.ref (.func 0)), .fx (.contNew ⟨0⟩)])
    (rest := [.fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]), .core (.plain .unreachable)])
    (.contNew hf0) (Or.inr (by simp)))) (Or.inr (by simp))

theorem step_resume {ti : TagInst} (ht : exS.tag? fr ⟨0⟩ = some (0, ti)) : SB P [some (C0 fi)]
    ([.label 1 [] [.contRef 0, .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]),
      .core (.plain .unreachable)]] ++ R) [none]
    ([.label 1 [] [.handler hs [.core (.ref (.func 0)), .core (.callRefType fi.type)],
      .core (.plain .unreachable)]] ++ R) := by
  have hr : [Silmaril.Wasm.Models.FX.OnClause.onLabel ⟨0⟩ ⟨0⟩].mapM
      (Silmaril.Wasm.Models.FX.resolve exS fr) = some hs := by
    simp [Silmaril.Wasm.Models.FX.resolve, ht]
  exact .seq (vs := []) (rest := R) (.ctxLabel (.seq (vs := [])
    (es := [.contRef 0, .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩])])
    (rest := [.core (.plain .unreachable)])
    (StepFX'.resume (vs := []) (k := 0) (C := C0 fi) rfl hr) (Or.inr (by simp))))
    (Or.inr (by simp))

/-- The body of `sus`, entered. -/
abbrev susCode : List AdminFX := [.frame 1 fr [.label 1 [] [.fx (.suspend ⟨0⟩), c7]]]

theorem step_invoke (hf0 : exS.funcs[0]? = some fi) (hc0 : fi.code = .host (.fx susF)) :
    SB P [none]
    ([.label 1 [] [.handler hs [.core (.ref (.func 0)), .core (.callRefType fi.type)],
      .core (.plain .unreachable)]] ++ R) [none]
    ([.label 1 [] [.handler hs susCode, .core (.plain .unreachable)]] ++ R) :=
  .seq (vs := []) (rest := R) (.ctxLabel (.seq (vs := [])
    (es := [.handler hs [.core (.ref (.func 0)), .core (.callRefType fi.type)]])
    (rest := [.core (.plain .unreachable)])
    (.ctxHandler (es' := susCode)
      (StepFX'.invoke (vs := []) (c := .callRefType fi.type) (F := susF) trivial hf0 hc0 rfl rfl))
    (Or.inr (by simp)))) (Or.inr (by simp))

end steps

/-! ## Suspension, the branch, and the second `resume` -/

theorem step_suspend (P : Profile) {ti : TagInst} (ht : exS.tag? fr ⟨0⟩ = some (0, ti)) :
    SB P [none] ([.label 1 [] [.handler hs susCode, .core (.plain .unreachable)]] ++ R)
      [none, some ⟨Es.plug⟩]
      ([.label 1 [] [.contRef 1, .core (.plain (.br ⟨0⟩)), .core (.plain .unreachable)]] ++ R) :=
  .seq (vs := []) (rest := R) (.ctxLabel (.seq (vs := [])
    (es := [.handler hs susCode]) (rest := [.core (.plain .unreachable)])
    (StepFX'.suspend (E := Es) (vs := []) (K := [none]) ht (by simp [CtxV.Handles]) (by rfl))
    (Or.inr (by simp)))) (Or.inr (by simp))

theorem step_br (P : Profile) :
    SB P [none, some ⟨Es.plug⟩]
      ([.label 1 [] [.contRef 1, .core (.plain (.br ⟨0⟩)), .core (.plain .unreachable)]] ++ R)
      [none, some ⟨Es.plug⟩] [.contRef 1, .fx (.resume ⟨0⟩ [])] :=
  .seq (vs := []) (es := [.label 1 [] [.contRef 1, .core (.plain (.br ⟨0⟩)),
      .core (.plain .unreachable)]]) (es' := [.contRef 1]) (rest := R)
    (StepFX'.brLabelZero (vs' := []) (vs := [.cont 1]) (rest := [.core (.plain .unreachable)])
      (by rfl) rfl)
    (Or.inr (by simp))

theorem step_resume₂ (P : Profile) :
    SB P [none, some ⟨Es.plug⟩] [.contRef 1, .fx (.resume ⟨0⟩ [])] [none, none]
      [.handler [] [.frame 1 fr [.label 1 [] [c7]]]] :=
  StepFX'.resume (vs := []) (k := 1) (C := ⟨Es.plug⟩) (hs' := []) rfl rfl

/-! ## Returning `7` -/

theorem step_label₁ (P : Profile) :
    SB P [none, none] [.handler [] [.frame 1 fr [.label 1 [] [c7]]]] [none, none]
      [.handler [] [.frame 1 fr [c7]]] :=
  .ctxHandler (.ctxFrame (.labelVals (vs := [.val v7])))

theorem step_frame₁ (P : Profile) :
    SB P [none, none] [.handler [] [.frame 1 fr [c7]]] [none, none] [.handler [] [c7]] :=
  .ctxHandler (.frameVals (vs := [.val v7]) rfl)

theorem step_handler (P : Profile) :
    SB P [none, none] [.handler [] [c7]] [none, none] [c7] :=
  .handlerVals (vs := [.val v7])

theorem step_label (P : Profile) :
    StepFX' P (noHostFX Nat) fxOf ⟨exS, [none, none], {}, wrap [c7]⟩
      ⟨exS, [none, none], {}, [.frame 1 fr [c7]]⟩ :=
  .ctxFrame (.labelVals (vs := [.val v7]))

theorem step_frame (P : Profile) :
    StepFX' P (noHostFX Nat) fxOf ⟨exS, [none, none], {}, [.frame 1 fr [c7]]⟩
      ⟨exS, [none, none], {}, cvals [v7]⟩ :=
  .frameVals (vs := [.val v7]) rfl

/-! ## The run -/

theorem internal_of_step (P : Profile) {s s' : Store (FXCode Nat)}
    {K K' : List (Option ContFX)} {f f' : Frame} {c c' : List AdminFX}
    (h : StepFX' P (noHostFX Nat) fxOf ⟨s, K, f, c⟩ ⟨s', K', f', c'⟩) :
    (fxEV P).Internal (s, ThreadV.fx K f c) (s', ThreadV.fx K' f' c') :=
  Or.inl ⟨_, _, _, rfl, h⟩

theorem run_ex_of (P : Profile) {fi₁ fi : FuncInst (FXCode Nat)} {ti : TagInst}
    (hf₁ : exS.funcs[1]? = some fi₁) (hc₁ : fi₁.code = .host (.fx runF))
    (hf0 : exS.funcs[0]? = some fi) (hc0 : fi.code = .host (.fx susF))
    (ht : exS.tag? fr ⟨0⟩ = some (0, ti)) :
    Silmaril.Wasm.Component.Engine.CoreEngine.Steps (fxEV P) (exS, (fxEV P).invoke (1 : Nat) [])
      (exS, ThreadV.fx [none, none] {} (cvals [v7])) := by
  have e0 : InternalV P (exS, ThreadV.core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 1 []))
      (exS, ThreadV.fx [] {} (wrap (runF.body.map Silmaril.Wasm.Models.FX.InstrFX.toAdmin))) :=
    Or.inr ⟨⟨runF, [], stat_enter P⟩, [], {}, _, rfl, step_enter P fi₁ hf₁ hc₁⟩
  exact .head e0 <| .head (internal_of_step P (lift P (step_block P))) <|
    .head (internal_of_step P (lift P (step_refFunc P))) <|
    .head (internal_of_step P (lift P (step_contNew P fi hf0))) <|
    .head (internal_of_step P (lift P (step_resume P fi ht))) <|
    .head (internal_of_step P (lift P (step_invoke P fi hf0 hc0))) <|
    .head (internal_of_step P (lift P (step_suspend P ht))) <|
    .head (internal_of_step P (lift P (step_br P))) <|
    .head (internal_of_step P (lift P (step_resume₂ P))) <|
    .head (internal_of_step P (lift P (step_label₁ P))) <|
    .head (internal_of_step P (lift P (step_frame₁ P))) <|
    .head (internal_of_step P (lift P (step_handler P))) <|
    .head (internal_of_step P (step_label P)) <|
    .single (internal_of_step P (step_frame P))

/-- **The run of `run`**: from the invocation, through a suspension of `sus` and its
resumption, to the FX thread at the value `7`. -/
theorem run_ex (P : Profile) :
    Silmaril.Wasm.Component.Engine.CoreEngine.Steps (fxEV P) (exS, (fxEV P).invoke (1 : Nat) [])
      (exS, ThreadV.fx [none, none] {} (cvals [v7])) := by
  obtain ⟨fi₁, hf₁, hc₁⟩ := f1
  obtain ⟨fi, hf0, hc0⟩ := f0
  obtain ⟨ti, ht⟩ := tag0
  exact run_ex_of P hf₁ hc₁ hf0 hc0 ht

/-- **The final status**: returned `7`. -/
theorem status_ex (P : Profile) :
    (fxEV P).status exS (ThreadV.fx [none, none] {} (cvals [v7])) = .returned (.values [y7]) :=
  (Silmaril.Proofs.Wasm.Component.FXEngineV.statusV_vals' (P := P) exS [none, none] {} [v7]).trans
    rfl

end Silmaril.Proofs.Wasm.Component.FXSuspend
