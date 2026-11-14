module

public import Silmaril.Wasm.FX.Logic.Iris.Defs
public import Silmaril.Wasm.FX.Logic.EveryRun.Thms
public import Iris.ProgramLogic.Adequacy

/-!
# The iris-lean `Language` for WasmFX: adequacy into the every-run logic

`hwp_of_adequate`: iris-lean's `adequate` for `run code` (with either stuckness: a `StepFX'`
run may get stuck, and the every-run `Safe` asks for no progress) gives the every-run weakest
precondition `HWP` of `Silmaril.Wasm.FX.Logic.EveryRun`. Every `StepFX'` run is a run of the
language (`reach_of_steps`), and every stopped outcome of a reachable configuration is a value
reached by its exit step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.IrisFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Stops Safe HWP)
open Silmaril.Wasm.FX.Logic.IrisFX
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)
open _root_.Iris _root_.Iris.ProgramLogic
open _root_.Iris.ProgramLogic.Language.Notation

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

theorem primStep_of_step {s s' : Store H} {K K' : Conts} {f f' : Frame} {c c' : List AdminFX}
    (h : StepFX' P noHost fx ⟨s, K, f, c⟩ ⟨s', K', f', c'⟩) :
    ((IExprFX.run c : IExprFX P fx), ((s, K, f) : IStateFX H)) -<([] : List Empty)>->
      (IExprFX.run c', ((s', K', f') : IStateFX H), []) :=
  ⟨rfl, rfl, .step h⟩

theorem primStep_of_stops {s : Store H} {K : Conts} {f : Frame} {c : List AdminFX}
    {o : OutcomeFX} (h : Stops s f o c) :
    ((IExprFX.run c : IExprFX P fx), ((s, K, f) : IStateFX H)) -<([] : List Empty)>->
      (IExprFX.done ⟨s, K, f, o⟩, ((s, K, f) : IStateFX H), []) :=
  ⟨rfl, rfl, .exit h⟩

theorem erasedStep_of_step {s s' : Store H} {K K' : Conts} {f f' : Frame} {c c' : List AdminFX}
    (h : StepFX' P noHost fx ⟨s, K, f, c⟩ ⟨s', K', f', c'⟩) :
    Language.ErasedStep ([(IExprFX.run c : IExprFX P fx)], ((s, K, f) : IStateFX H))
      ([IExprFX.run c'], (s', K', f')) :=
  ⟨[], Language.Step.atomic (primStep_of_step h) [] []⟩

theorem erasedStep_of_stops {s : Store H} {K : Conts} {f : Frame} {c : List AdminFX}
    {o : OutcomeFX} (h : Stops s f o c) :
    Language.ErasedStep ([(IExprFX.run c : IExprFX P fx)], ((s, K, f) : IStateFX H))
      ([IExprFX.done ⟨s, K, f, o⟩], (s, K, f)) :=
  ⟨[], Language.Step.atomic (primStep_of_stops h) [] []⟩

/-- Every `StepFX'` run is a run of the language. -/
theorem reach_of_steps {s : Store H} {K : Conts} {f : Frame} {c : List AdminFX} :
    ∀ {d : ConfigFX H}, StepsFX' P noHost fx ⟨s, K, f, c⟩ d →
      ([(IExprFX.run c : IExprFX P fx)], ((s, K, f) : IStateFX H)) -·->ₜₚ*
        ([IExprFX.run d.code], (d.store, d.conts, d.frame))
  | _, .refl => .refl
  | _, .tail hs h => .tail (reach_of_steps hs) (erasedStep_of_step h)

/-- **Iris adequacy gives every-run safety** of every reachable configuration. -/
theorem safe_of_adequate {st : _root_.Iris.Stuckness} {s : Store H} {K : Conts} {f : Frame}
    {code : List AdminFX} {Q : PostFX H}
    (had : adequate st (IExprFX.run code : IExprFX P fx) ((s, K, f) : IStateFX H)
      (fun r _ => Q r.store r.conts r.frame r.out)) :
    ∀ (n : Nat) (d : ConfigFX H), StepsFX' P noHost fx ⟨s, K, f, code⟩ d → Safe P fx Q n d
  | 0, _, _ => trivial
  | n + 1, d, hs =>
    ⟨fun o ho => had.adequate_result [] (d.store, d.conts, d.frame) ⟨d.store, d.conts, d.frame, o⟩
        ((reach_of_steps hs).tail (erasedStep_of_stops ho)),
      fun d' h => safe_of_adequate had n d' (hs.tail h)⟩

/-- **Iris adequacy gives the every-run weakest precondition.** -/
theorem hwp_of_adequate {st : _root_.Iris.Stuckness} {s : Store H} {K : Conts} {f : Frame}
    {code : List AdminFX} {Q : PostFX H}
    (had : adequate st (IExprFX.run code : IExprFX P fx) ((s, K, f) : IStateFX H)
      (fun r _ => Q r.store r.conts r.frame r.out)) : HWP P fx s K f code Q :=
  fun n => safe_of_adequate had n _ .refl

end Silmaril.Proofs.Wasm.FX.Logic.IrisFX
