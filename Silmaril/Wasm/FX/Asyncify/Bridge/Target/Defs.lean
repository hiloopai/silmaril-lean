module

public import Silmaril.Wasm.FX.Asyncify.Bridge.Defs

/-!
# The target half of the tool as an instance: definitions

`Task.tool_tgt_sim` (`Silmaril.Wasm.FX.Asyncify.Bridge`) asks for a stuttering simulation in the
family's sense (`SimRel`: every source step matched by a **positive** number of target steps)
from the family's whole-program host target on `trP P.env` to the tool's asyncified program
under its protocol. This module has the pieces to refute it and to restate it:

* `famStep Q test K`: the family's host target `htstep Q test K` as a closed system of the tool
  (`Tool.SRes`), its stops observed with the host state and read as tool observations
  (`toolOut`), so that the tool's stuttering simulations (`Tool.IsSim`, with a measure for steps
  matched by no target step) compare it with the tool's target;
* `NoDivStop step`: no step stops with the observation `diverges` (true of both systems);
* `calmFn`, `calmP`, `unitHost`: a program without imports whose one function returns its
  parameter, and a host that answers nothing; the family's target takes more steps on it than
  the tool's; `saFn`, `saP`: `sleep-add`, on which the tool's target takes more.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Bridge

open Silmaril.Wasm
open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify.Host

variable {σ : Type}

/-- **The family's host target as a tool system**: a stop is observed with the host state and
read as a tool observation. -/
def famStep (Q : Prog (TIns KV)) (test : KV → Bool) (K : KHost KV σ) (y : TCfg KV × σ) :
    Tool.SRes (TCfg KV × σ) σ :=
  match htstep Q test K y with
  | .next y' => .next y'
  | .stop o => .stop (toolOut (HOut.ofOutcome y.2 o))

/-- No step stops with the observation `diverges`. -/
def NoDivStop {X : Type} (step : X → Tool.SRes X σ) : Prop :=
  ∀ x o, step x = .stop o → o ≠ .diverges

/-- `(func (param i32) (result i32) local.get 0)`, no statements. -/
def calmFn : Tool.FnSrc := ⟨1, 0, 1, [], [.localGet (Tool.lidx 0)]⟩

/-- A program without imports: the function `calmFn` (index 0). -/
def calmP : Tool.Prog := ⟨[], [calmFn]⟩

/-- `sleep-add` in statement form: `local.get 0; call 0; local.set 1`, tail
`local.get 1; local.get 0; i32.add`, import 0 with one argument and one result. -/
def saFn : Tool.FnSrc := ⟨1, 1, 1, [.call ⟨Fin.ofNat _ 0⟩ [Tool.lidx 0] [Tool.lidx 1]],
  [.localGet (Tool.lidx 1), .localGet (Tool.lidx 0), .intBinOp .i32 .add]⟩

/-- The program of `sleep-add`: import 0, then `saFn` (index 1). -/
def saP : Tool.Prog := ⟨[(1, 1)], [saFn]⟩

/-- A host that echoes the arguments (never called on `calmP`). -/
def unitHost : Tool.Host Unit := ⟨fun s _ as => (s, as)⟩

end Silmaril.Wasm.FX.Asyncify.Bridge
