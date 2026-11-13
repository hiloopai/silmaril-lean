module

public import Silmaril.Wasm.FX.Logic.EveryRun.Defs
public import Iris.ProgramLogic.Language

/-!
# An iris-lean `Language` for WasmFX: definitions

A start on an Iris logic for WasmFX: an instance of upstream iris-lean's
`Iris.ProgramLogic.Language` for `StepFX'` (`Silmaril.Wasm.Models.FXV`) without host calls, for
every profile `P` and FX function table `fx` (indices of the expression type `IExprFX P fx`),
following `Silmaril.Wasm.Logic.IrisWasm` (the Core 3.0 language).

* The state is the Core store, the **continuation store** and the current frame.
* An expression is running FX code `run c` or a finished run `done r` (`ResFX`: the final
  stores, frame and outcome).
* A primitive step is a `StepFX'` step, or the **exit step** from code that has stopped with an
  outcome `o` (`Silmaril.Wasm.FX.Logic.EveryRun.Stops`: values, a branch, `return`, a trap, an
  exception, or an unhandled `suspend` / `switch`) to `done`. Stopped code with several outcomes
  (a `suspend` under values stops with every split) has an exit step for each.
* The values are the finished runs, so `val_stuck` holds by construction.

Adequacy into the every-run logic is `Silmaril.Wasm.FX.Logic.Iris.Thms`. Open: a state
interpretation for the continuation store (one-shot ownership of slots) and weakest-precondition
rules for the stack-switching instructions.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.IrisFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Stops)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)
open _root_.Iris.ProgramLogic

variable {H : Type}

/-- A finished run: the final stores and frame, and the outcome. -/
structure ResFX (H : Type) where
  /-- The final Core store. -/
  store : Store H
  /-- The final continuation store. -/
  conts : Conts
  /-- The final frame. -/
  frame : Frame
  /-- How the code stopped. -/
  out : OutcomeFX

/-- The state: the Core store, the continuation store and the current frame. -/
abbrev IStateFX (H : Type) := Store H × Conts × Frame

/-- Expressions: running FX code or a finished run. -/
inductive IExprFX {H : Type} (P : Profile) (fx : H → Option FuncFX) : Type where
  /-- FX code running in the current state. -/
  | run (code : List AdminFX)
  /-- A finished run. -/
  | done (r : ResFX H)

variable {P : Profile} {fx : H → Option FuncFX}

/-- Primitive steps: a `StepFX'` step, or the exit of stopped code. -/
inductive IStepFX : IExprFX P fx → IStateFX H → IExprFX P fx → IStateFX H → Prop where
  /-- A step of `StepFX' P noHost fx`. -/
  | step {s s' : Store H} {K K' : Conts} {f f' : Frame} {c c' : List AdminFX}
      (h : StepFX' P noHost fx ⟨s, K, f, c⟩ ⟨s', K', f', c'⟩) :
      IStepFX (.run c) (s, K, f) (.run c') (s', K', f')
  /-- Code that has stopped with outcome `o` finishes, keeping the state. -/
  | exit {s : Store H} {K : Conts} {f : Frame} {c : List AdminFX} {o : OutcomeFX}
      (h : Stops s f o c) : IStepFX (.run c) (s, K, f) (.done ⟨s, K, f, o⟩) (s, K, f)

/-- The value of an expression: the result of a finished run. -/
def IExprFX.toVal : IExprFX P fx → Option (ResFX H)
  | .run _ => none
  | .done r => some r

instance instToVal : ToVal (IExprFX P fx) (ResFX H) where
  toVal := IExprFX.toVal
  ofVal := .done
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | run c => cases h
    | done r => cases h; rfl
  toVal_coe _ := rfl

instance instPrimStep : PrimStep (IExprFX P fx) (IStateFX H) (List Empty) where
  primStep
    | (e, σ), obs, (e', σ', efs) => obs = [] ∧ efs = [] ∧ IStepFX e σ e' σ'

/-- **The language.** No observations, no forked threads. -/
instance instLanguage : Language (IExprFX P fx) (IStateFX H) Empty (ResFX H) :=
  { instToVal, instPrimStep with
    val_stuck := fun {e σ obs e' σ' eₜ} h => by
      obtain ⟨-, -, hs⟩ := h
      cases hs <;> rfl }

end Silmaril.Wasm.FX.Logic.IrisFX
