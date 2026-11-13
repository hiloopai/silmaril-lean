module

public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Caller.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Finite.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Cleanup.Thms
/-! Actual finite slot-bearing source traces and the existing full native optimizer. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Slots.Finite
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract
open Relation
open Validation.Finite Validation.Machine

def AdmittedFunction (function : Mir.Func) : Prop :=
  ∀ block ∈ function.blocks.toList, Slots.Admitted block.instrs.toList


end Silmaril.Compiler.Native.Optimize.Validation.Slots.Finite
