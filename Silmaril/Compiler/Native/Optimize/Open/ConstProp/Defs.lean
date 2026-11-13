module

public import Silmaril.Compiler.Native.Semantics.OpenFrame.Defs
public import Silmaril.Compiler.Mir.ConstProp.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Machine.Defs
/-! Actual constant propagation under explicit native open-address/call meanings.
The original checked analysis and rewriting functions are reused unchanged. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Open.ConstProp

open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Semantics

abbrev Facts := Mir.ConstProp.Facts

/-- Actual checked source entry facts, independently of rewritten execution. -/
def Entry (function : Mir.Func) (state : OpenFrame.State) : Prop :=
  ∃ facts, Mir.ConstProp.entryAt (Mir.ConstProp.entryFacts function) state.label = some facts ∧
    Mir.ConstProp.Holds facts state.frame

end Silmaril.Compiler.Native.Optimize.Open.ConstProp
