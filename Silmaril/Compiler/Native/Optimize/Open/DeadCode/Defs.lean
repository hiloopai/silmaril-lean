module

public import Silmaril.Compiler.Native.Semantics.OpenFrame.Defs
public import Silmaril.Compiler.Mir.DeadCode.Defs
/-! Actual DCE under explicit native open meanings. Deleted definitions need
only actual live-register agreement; slots and memory remain observable. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Open.DeadCode

open Silmaril.Compile
abbrev LiveSet := Mir.DeadCode.RSet
abbrev Agree := Mir.DeadCode.Agree

/-- Exactly the mapped branch of the actual checked function pass. -/
def checkedFunction (certificate : Array LiveSet) (function : Mir.Func) : Mir.Func :=
  { function with blocks := function.blocks.map (Mir.DeadCode.dceBlock certificate) }

end Silmaril.Compiler.Native.Optimize.Open.DeadCode
