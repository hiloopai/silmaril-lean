module

public import Silmaril.Compiler.Native.Optimize.Validation.Floating.Caller.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Finite.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Cleanup.Thms
/-! Actual finite successful primitive/floating source traces and the existing native optimizer.
Address instructions and calls remain excluded by independent syntax admission. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Floating.Finite
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract
open Relation
open Validation.Finite Validation.Machine

def AdmittedFunction (function : Mir.Func) : Prop :=
  ∀ block ∈ function.blocks.toList, Floating.Admitted block.instrs.toList

end Silmaril.Compiler.Native.Optimize.Validation.Floating.Finite
