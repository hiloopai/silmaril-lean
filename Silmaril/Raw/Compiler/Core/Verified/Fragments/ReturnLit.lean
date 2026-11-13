module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.ReturnLit.Defs
/-! # Fragment: an explicit `return n;` of an integer literal -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- `ReturnLit.recognize`'s literal, returned by `ConstLink.link`. -/
def returnLit : Fragment := .ofConst ReturnLit.recognize ReturnLit.recognize_sound

end Silmaril.Compile.Core.Verified.Fragments
