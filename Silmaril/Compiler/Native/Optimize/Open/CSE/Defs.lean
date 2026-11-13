module

public import Silmaril.Compiler.Native.Semantics.OpenFrame.Defs
public import Silmaril.Compiler.Mir.CSE.Defs
/-! Actual common-subexpression elimination under explicit native open meanings.
The original rewrite functions and effect classification are unchanged. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Open.CSE

abbrev Facts := Silmaril.Compile.Mir.CSE.Facts

end Silmaril.Compiler.Native.Optimize.Open.CSE
