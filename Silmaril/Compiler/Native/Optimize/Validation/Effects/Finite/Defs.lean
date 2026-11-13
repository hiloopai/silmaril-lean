module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Caller.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Finite.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Cleanup.Thms
/-! Actual finite successful Lir.Op source traces and the existing native optimizer.
Floating/address instructions and calls remain excluded by exact admission. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects.Finite
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract
open Relation
open Validation.Finite Validation.Machine

def AdmittedFunction (function : Mir.Func) : Prop :=
  ∀ block ∈ function.blocks.toList, Effects.Admitted block.instrs.toList


end Silmaril.Compiler.Native.Optimize.Validation.Effects.Finite
