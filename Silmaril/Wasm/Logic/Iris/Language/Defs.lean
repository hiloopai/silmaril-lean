module

public import Silmaril.Wasm.Logic.Hoare.Defs
public import Iris.ProgramLogic.Language

/-!
# An iris-lean `Language` for Wasm Core 3.0: definitions

An instance of upstream iris-lean's `Iris.ProgramLogic.Language` for pinned
silmaril-lean's Core 3.0 small-step semantics `Step P host`, for **every profile**
`P` and **every host relation** `host` (both are indices of the expression type
`IExpr P host`, so one instance serves all of them).

* An expression is either running code `run c` or a finished run `done r`. The
  state is the store and the current frame. A finished run records its outcome
  together with the store and frame it ended in (`Res`), so postconditions of the
  weakest precondition can speak about the final store as in
  `Silmaril.Wasm.Logic.Hoare.HWP`.
* A primitive step of `run c` is either a Core 3.0 step (`IStep.step`), or the
  administrative **exit step** `IStep.exit`, from code `c` that has left with an
  outcome `o` (`Silmaril.Wasm.Logic.Hoare.Exits o c`: values, a branch, a `return`,
  a trap, an exception or a tail call) to `done ⟨s, f, o⟩`, keeping the state.
* The values of the language are the finished runs: `toVal (done r) = some r`
  and `toVal (run c) = none`, so `Language.val_stuck` holds by construction.

The outcomes are Silmaril's (`Silmaril.Wasm.Logic.Core.Outcome`), so traps, exceptions
(`throw a`), branches and returns out of the code, and tail calls are all values
of the language: the postcondition of an Iris WP is indexed by outcome, like the
every-run logic `Silmaril.Wasm.Logic.Hoare`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.Logic.Hoare (Exits)
open _root_.Iris.ProgramLogic

variable {H : Type}

/-- A finished run: the final store and frame, and the outcome. -/
structure Res (H : Type) where
  /-- The final store. -/
  store : Store H
  /-- The final frame. -/
  frame : Frame
  /-- How the code left. -/
  out : Outcome

/-- The state of the language: the store and the current frame. -/
abbrev IState (H : Type) := Store H × Frame

/-- Expressions: running code or a finished run. `P` and `host` are indices only,
fixing the semantics the expression runs under. -/
inductive IExpr {H : Type} (P : Profile) (host : HostSemantics H) : Type where
  /-- Code running in the current state. -/
  | run (code : List Admin)
  /-- A finished run. -/
  | done (r : Res H)

variable {P : Profile} {host : HostSemantics H}

/-- Primitive steps: a Core 3.0 step, or the exit of code that has left. -/
inductive IStep : IExpr P host → IState H → IExpr P host → IState H → Prop where
  /-- A step of `Step P host`. -/
  | step {s s' : Store H} {f f' : Frame} {c c' : List Admin}
      (h : Step P host ⟨s, f, c⟩ ⟨s', f', c'⟩) : IStep (.run c) (s, f) (.run c') (s', f')
  /-- Code that has left with outcome `o` finishes, keeping the state. -/
  | exit {s : Store H} {f : Frame} {c : List Admin} {o : Outcome} (h : Exits o c) :
      IStep (.run c) (s, f) (.done ⟨s, f, o⟩) (s, f)

/-- The value of an expression: the result of a finished run. -/
def IExpr.toVal : IExpr P host → Option (Res H)
  | .run _ => none
  | .done r => some r

instance instToVal : ToVal (IExpr P host) (Res H) where
  toVal := IExpr.toVal
  ofVal := .done
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | run c => cases h
    | done r => cases h; rfl
  toVal_coe _ := rfl

instance instPrimStep : PrimStep (IExpr P host) (IState H) (List Empty) where
  primStep
    | (e, σ), obs, (e', σ', efs) => obs = [] ∧ efs = [] ∧ IStep e σ e' σ'

/-- **The language.** No observations, no forked threads. -/
instance instLanguage : Language (IExpr P host) (IState H) Empty (Res H) :=
  { instToVal, instPrimStep with
    val_stuck := fun {e σ obs e' σ' eₜ} h => by
      obtain ⟨-, -, hs⟩ := h
      cases hs <;> rfl }

end Silmaril.Wasm.Logic.IrisWasm
