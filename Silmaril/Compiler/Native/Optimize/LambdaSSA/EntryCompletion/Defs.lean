module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.BlockSemantics.Defs
/-! A concrete completed input frame and one-sided agreement for defined reads.
Completing missing input values can enable previously failing executions. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.EntryCompletion
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Scope)
open Silmaril.Machine.Lir (Word)

def DefinedAgreement (scope : Scope Nat) (source target : Frame Nat) : Prop :=
  ∀ register, scope.HasReg register → ∀ word,
    source.get register = some word → target.get register = some word

def arguments (source : Frame Nat) (inputs : List Nat) : List Word :=
  inputs.map (fun register => (source.get register).getD 0)

def completeFrom (source initial : Frame Nat) : List Nat → Frame Nat
  | [] => initial
  | register :: rest => completeFrom source
      (initial.set register ((source.get register).getD 0)) rest

def complete (source : Frame Nat) (inputs : List Nat) : Frame Nat :=
  completeFrom source .empty inputs

end Silmaril.Compiler.Native.Optimize.LambdaSSA.EntryCompletion
