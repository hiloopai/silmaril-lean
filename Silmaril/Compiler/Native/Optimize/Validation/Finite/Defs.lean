module

public import Silmaril.Compiler.Native.Optimize.Validation.Machine.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ContextualSoundness.Defs
/-! Finite successful actual Mir machine traces and exact local-SSA boundary relation. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Finite
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract
open Relation

inductive Outcome where
  | returned (words : List Lir.Word) (memory : Lir.Memory)
  | trapped (memory : Lir.Memory)

def Outcome.result : Outcome → MirSem.Result
  | .returned words memory => .returned words memory
  | .trapped memory => .trapped memory

def Outcome.behavior : Outcome → Lir.Behavior
  | .returned words memory => .returned words memory
  | .trapped memory => .trapped memory

inductive Run (units : Array Mir.Unit) (placement : MirSem.Placement) (outcome : Outcome) : Nat → MirSem.State → Prop where
  | done {state} (terminal : MirSem.step units placement state = outcome.result) : Run units placement outcome 0 state
  | next {count state later} (step : MirSem.Step units placement state later)
      (rest : Run units placement outcome count later) : Run units placement outcome (count + 1) state

/-- The exact local-SSA stage used inside optimizeWith, before cleanup passes. -/
def versionUnits (cfg : Config) (units : Array Mir.Unit) : Array Mir.Unit :=
  units.map fun unit => { unit with funcs := unit.funcs.map (versionFunc cfg) }

def AdmittedFunction (function : Mir.Func) : Prop :=
  ∀ block ∈ function.blocks.toList, Lists.Admitted block.instrs.toList

/-- Original and actual mapped functions agree at a control-flow boundary.
Fresh registers may differ, and low registers and slots may remain partial. -/
def BoundaryRelated (cfg : Config) (function : Mir.Func) (source candidate : MirSem.State) : Prop :=
  ∃ label sourceFrame candidateFrame memory,
    source = ⟨function, label, 0, sourceFrame, [], memory⟩ ∧
    candidate = ⟨versionFunc cfg function, label, 0, candidateFrame, [], memory⟩ ∧
    PureSoundness.FrameAgrees (freshBase function) sourceFrame candidateFrame


end Silmaril.Compiler.Native.Optimize.Validation.Finite
