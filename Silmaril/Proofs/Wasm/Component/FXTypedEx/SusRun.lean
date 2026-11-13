module

public import Silmaril.Proofs.Wasm.Component.FXTypedEx.Inst
public import Silmaril.Proofs.Wasm.Component.FXTyped.Arity
public import Silmaril.Proofs.Wasm.Component.FXEngineV.Vals

/-!
# The suspending component: a run of `run`

The run of `susC`'s export `run` in the `fxEV P` engine instance of its module (kernel-evaluated,
`susHJ`): it enters `run` (`internalV_enter`), makes a continuation of `sus` and resumes it under a
handler for tag 0, `sus` **suspends**, the handler's branch carries the continuation out of the
block, the second `resume` runs `sus` to its end, `run` drops the `7` and returns no value
(`run_steps`, `run_status`). This follows `FXSuspend.run_ex`, in the store of `susC` and with the
final `drop`. So `some []` is an outcome of the engine (`run_out`), and the component of
`susC_refToSpec` does suspend.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXTypedEx

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (AdminFX ContFX FuncFX HClause InstrFX cvals)
open Silmaril.Wasm.Models.FXV (StepFX' CtxV FVal fvals)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.FXEngine
  Silmaril.Wasm.Component.FXEngineV Silmaril.Wasm.Component.FXRefV Silmaril.Wasm.Component.FXTypedEx
open Silmaril.Wasm.Component.FXSuspend (susDecl blockBody)
open Silmaril.Proofs.Wasm.Component.FXTyped (FXAt internalV_enter enterCode)
open Silmaril.Wasm.Numerics (Profile)

/-! ## The instance -/

/-- The instantiation of `susC`'s module. -/
def susPrep : Option (Store (FXCode Nat) × InstFX × Option Nat) :=
  prepareFXV? {} (susC.emb susC.mod) []

/-- Its store. -/
def susS : Store (FXCode Nat) := (susPrep.map (·.1)).getD {}

/-- Its instance. -/
def susI : InstFX := (susPrep.map (·.2.1)).getD ⟨{}, []⟩

/-- The instance seen by the FX functions (`sus` at address 0, `run` at address 1). -/
abbrev susI' : ModuleInst := fxInst susI.core 0 2

/-- `sus`. -/
abbrev susF' : FuncFX := susDecl.func susI'

/-- `run`. -/
abbrev runF' : FuncFX := run0Decl.func susI'

/-- The frame of `run` and of `sus`. -/
abbrev frS : Frame := Frame.forCall susI' [] []

theorem susPrep_eq : susPrep = some (susS, susI, none) := by rfl

theorem run_fxAt : FXAt susS 1 runF' run0Decl.type := ⟨by rfl, rfl⟩

theorem sus_f0 : susS.funcs[0]? =
    some ⟨SingleThreaded.ofFlatType susDecl.type, {}, .host (.fx susF')⟩ := by rfl

theorem sus_tag_map : (susS.tag? frS ⟨0⟩).map (·.1) = some 0 := by rfl

theorem sus_tag : ∃ ti, susS.tag? frS ⟨0⟩ = some (0, ti) := by
  rcases h : susS.tag? frS ⟨0⟩ with _ | ⟨a, ti⟩
  · have e := sus_tag_map
    rw [h] at e
    cases e
  · have e : some a = some 0 := by simpa [h] using sus_tag_map
    exact ⟨ti, by rw [Option.some.inj e]⟩

/-- **The engine instance of `susC`'s module.** -/
theorem susHJ (P : Profile) :
    instOf (fxEV P) (susC.emb susC.mod) [] susC.mod.exports = some ⟨susS, [(0 : Nat), (1 : Nat)]⟩ := by
  unfold instOf
  rw [show (fxEV P).prepare? = prepareFXV? from rfl]
  change (match susPrep with | some (s', inst, none) => _ | _ => none) = _
  rw [susPrep_eq]
  rfl

/-! ## The steps of `run`'s body -/

/-- `i32.const 7`. -/
abbrev c7 : AdminFX := .core (.plain (.intConst .i32 7))

/-- The rest of `run`'s body after the block. -/
abbrev R : List AdminFX := [.fx (.resume ⟨0⟩ []), .core (.plain .drop)]

/-- The resolved clause `(on 0 0)`. -/
abbrev hs : List HClause := [.onLabel 0 ⟨0⟩]

/-- The context captured by `suspend`. -/
abbrev Es : CtxV := .frame 1 frS (.label 1 [] (.seq [] .hole [c7]))

/-- A step of `run`'s body. -/
abbrev SB (P : Profile) (K : List (Option ContFX)) (c : List AdminFX)
    (K' : List (Option ContFX)) (c' : List AdminFX) : Prop :=
  StepFX' P (noHostFX Nat) fxOf ⟨susS, K, frS, c⟩ ⟨susS, K', frS, c'⟩

/-- `run`'s frame and label around `c`. -/
abbrev wrap (c : List AdminFX) : List AdminFX := [.frame 0 frS [.label 0 [] c]]

theorem lift (P : Profile) {K K' : List (Option ContFX)} {c c' : List AdminFX}
    (h : SB P K c K' c') :
    (fxEV P).Internal (susS, ThreadV.fx K {} (wrap c)) (susS, ThreadV.fx K' {} (wrap c')) :=
  Or.inl ⟨_, _, _, rfl, .ctxFrame (.ctxLabel h)⟩

section steps

variable (P : Profile)

theorem s_block : SB P [] ([.block (.value (.num (.int .i32))) blockBody] ++ R) []
    ([.label 1 [] (blockBody.map InstrFX.toAdmin)] ++ R) :=
  .seq (vs := []) (rest := R) (.block (vs := []) (t₁ := []) (t₂ := [.num (.int .i32)]) (by rfl) rfl)
    (Or.inr (by simp))

theorem s_refFunc : SB P []
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
abbrev C0 : ContFX :=
  ⟨fun c => c ++ [.core (.ref (.func 0)),
    .core (.callRefType (SingleThreaded.ofFlatType susDecl.type))]⟩

theorem s_contNew : SB P []
    ([.label 1 [] [.core (.ref (.func 0)), .fx (.contNew ⟨0⟩),
      .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]), .core (.plain .unreachable)]] ++ R) [some C0]
    ([.label 1 [] [.contRef 0, .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]),
      .core (.plain .unreachable)]] ++ R) :=
  .seq (vs := []) (rest := R) (.ctxLabel (.seq (vs := [])
    (es := [.core (.ref (.func 0)), .fx (.contNew ⟨0⟩)])
    (rest := [.fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]), .core (.plain .unreachable)])
    (.contNew sus_f0) (Or.inr (by simp)))) (Or.inr (by simp))

theorem s_resume {ti : TagInst} (ht : susS.tag? frS ⟨0⟩ = some (0, ti)) : SB P [some C0]
    ([.label 1 [] [.contRef 0, .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]),
      .core (.plain .unreachable)]] ++ R) [none]
    ([.label 1 [] [.handler hs [.core (.ref (.func 0)),
      .core (.callRefType (SingleThreaded.ofFlatType susDecl.type))],
      .core (.plain .unreachable)]] ++ R) := by
  have hr : [Silmaril.Wasm.Models.FX.OnClause.onLabel ⟨0⟩ ⟨0⟩].mapM
      (Silmaril.Wasm.Models.FX.resolve susS frS) = some hs := by
    simp [Silmaril.Wasm.Models.FX.resolve, ht]
  exact .seq (vs := []) (rest := R) (.ctxLabel (.seq (vs := [])
    (es := [.contRef 0, .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩])])
    (rest := [.core (.plain .unreachable)])
    (StepFX'.resume (vs := []) (k := 0) (C := C0) rfl hr) (Or.inr (by simp))))
    (Or.inr (by simp))

/-- The body of `sus`, entered. -/
abbrev susCode : List AdminFX := [.frame 1 frS [.label 1 [] [.fx (.suspend ⟨0⟩), c7]]]

theorem s_invoke : SB P [none]
    ([.label 1 [] [.handler hs [.core (.ref (.func 0)),
      .core (.callRefType (SingleThreaded.ofFlatType susDecl.type))],
      .core (.plain .unreachable)]] ++ R) [none]
    ([.label 1 [] [.handler hs susCode, .core (.plain .unreachable)]] ++ R) :=
  .seq (vs := []) (rest := R) (.ctxLabel (.seq (vs := [])
    (es := [.handler hs [.core (.ref (.func 0)),
      .core (.callRefType (SingleThreaded.ofFlatType susDecl.type))]])
    (rest := [.core (.plain .unreachable)])
    (.ctxHandler (es' := susCode)
      (StepFX'.invoke (vs := []) (F := susF') trivial sus_f0 rfl rfl rfl))
    (Or.inr (by simp)))) (Or.inr (by simp))

theorem s_suspend {ti : TagInst} (ht : susS.tag? frS ⟨0⟩ = some (0, ti)) :
    SB P [none] ([.label 1 [] [.handler hs susCode, .core (.plain .unreachable)]] ++ R)
      [none, some ⟨Es.plug⟩]
      ([.label 1 [] [.contRef 1, .core (.plain (.br ⟨0⟩)), .core (.plain .unreachable)]] ++ R) :=
  .seq (vs := []) (rest := R) (.ctxLabel (.seq (vs := [])
    (es := [.handler hs susCode]) (rest := [.core (.plain .unreachable)])
    (StepFX'.suspend (E := Es) (vs := []) (K := [none]) ht (by simp [CtxV.Handles]) (by rfl))
    (Or.inr (by simp)))) (Or.inr (by simp))

theorem s_br : SB P [none, some ⟨Es.plug⟩]
    ([.label 1 [] [.contRef 1, .core (.plain (.br ⟨0⟩)), .core (.plain .unreachable)]] ++ R)
    [none, some ⟨Es.plug⟩] ([.contRef 1] ++ R) :=
  .seq (vs := []) (es := [.label 1 [] [.contRef 1, .core (.plain (.br ⟨0⟩)),
      .core (.plain .unreachable)]]) (es' := [.contRef 1]) (rest := R)
    (StepFX'.brLabelZero (vs' := []) (vs := [.cont 1]) (rest := [.core (.plain .unreachable)])
      (by rfl) rfl)
    (Or.inr (by simp))

/-- The handler around the resumed `sus`, before the final `drop`. -/
abbrev D : List AdminFX := [.core (.plain .drop)]

theorem s_resume₂ : SB P [none, some ⟨Es.plug⟩] ([.contRef 1] ++ R) [none, none]
    ([.handler [] [.frame 1 frS [.label 1 [] [c7]]]] ++ D) :=
  .seq (vs := []) (es := [.contRef 1, .fx (.resume ⟨0⟩ [])]) (rest := D)
    (StepFX'.resume (vs := []) (k := 1) (C := ⟨Es.plug⟩) (hs' := []) rfl rfl) (Or.inr (by simp))

theorem s_label₁ : SB P [none, none] ([.handler [] [.frame 1 frS [.label 1 [] [c7]]]] ++ D)
    [none, none] ([.handler [] [.frame 1 frS [c7]]] ++ D) :=
  .seq (vs := []) (rest := D) (.ctxHandler (.ctxFrame (.labelVals (vs := [.val (.num ⟨.int .i32, 7⟩)]))))
    (Or.inr (by simp))

theorem s_frame₁ : SB P [none, none] ([.handler [] [.frame 1 frS [c7]]] ++ D) [none, none]
    ([.handler [] [c7]] ++ D) :=
  .seq (vs := []) (rest := D) (.ctxHandler (.frameVals (vs := [.val (.num ⟨.int .i32, 7⟩)]) rfl))
    (Or.inr (by simp))

theorem s_handler : SB P [none, none] ([.handler [] [c7]] ++ D) [none, none] ([c7] ++ D) :=
  .seq (vs := []) (rest := D) (.handlerVals (vs := [.val (.num ⟨.int .i32, 7⟩)])) (Or.inr (by simp))

theorem s_drop : SB P [none, none] ([c7] ++ D) [none, none] [] :=
  .core (cs := [.plain (.intConst .i32 7), .plain .drop]) (cs' := [])
    (.parametric (.drop (.num ⟨.int .i32, 7⟩)))

end steps

/-! ## The run -/

theorem enter_code : [enterCode runF' (([] : List Flat).map SingleThreaded.ofFlat)] =
    wrap ([.block (.value (.num (.int .i32))) blockBody] ++ R) := rfl

/-- **The run of `run`**: through a suspension of `sus` and its resumption, to no value. -/
theorem run_steps (P : Profile) :
    Silmaril.Wasm.Component.Engine.CoreEngine.Steps (fxEV P) (susS, (fxEV P).invoke (1 : Nat) [])
      (susS, ThreadV.fx [none, none] {} (cvals [])) := by
  obtain ⟨ti, ht⟩ := sus_tag
  have e0 := internalV_enter (P := P) run_fxAt (xs := []) rfl
  rw [enter_code] at e0
  have eL : (fxEV P).Internal (susS, ThreadV.fx [none, none] {} (wrap []))
      (susS, ThreadV.fx [none, none] {} [.frame 0 frS (fvals [])]) :=
    Or.inl ⟨_, _, _, rfl, .ctxFrame (.labelVals (vs := []))⟩
  have eF : (fxEV P).Internal (susS, ThreadV.fx [none, none] {} [.frame 0 frS (fvals [])])
      (susS, ThreadV.fx [none, none] {} (cvals [])) :=
    Or.inl ⟨_, _, _, rfl, .frameVals (vs := []) rfl⟩
  exact .head e0 <| .head (lift P (s_block P)) <| .head (lift P (s_refFunc P)) <|
    .head (lift P (s_contNew P)) <| .head (lift P (s_resume P ht)) <|
    .head (lift P (s_invoke P)) <| .head (lift P (s_suspend P ht)) <|
    .head (lift P (s_br P)) <| .head (lift P (s_resume₂ P)) <| .head (lift P (s_label₁ P)) <|
    .head (lift P (s_frame₁ P)) <| .head (lift P (s_handler P)) <| .head (lift P (s_drop P)) <|
    .head eL <| .single eF

/-- **The final status**: returned, no value. -/
theorem run_status (P : Profile) :
    (fxEV P).status susS (ThreadV.fx [none, none] {} (cvals [])) = .returned (.values []) :=
  (Silmaril.Proofs.Wasm.Component.FXEngineV.statusV_vals' (P := P) susS [none, none] {} []).trans rfl

/-- **`run` returns no value**, after a suspension and a resumption. -/
theorem run_out (P : Profile) :
    some [] ∈ engineOut (fxEV P) ⟨susS, [(0 : Nat), (1 : Nat)]⟩ 1 (lowerArgs [] []) :=
  ⟨(1 : Nat), susS, _, rfl, run_steps P, Or.inl ⟨_, run_status P, rfl⟩⟩

end Silmaril.Proofs.Wasm.Component.FXTypedEx
