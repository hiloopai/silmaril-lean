module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.ReturnConst.Defs
/-! # Fragment: `main` returns an integer literal through its saved return label -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- `ReturnConst.recognize`'s literal, returned by `ConstLink.link`. -/
def returnConst : Fragment := .ofConst ReturnConst.recognize ReturnConst.recognize_sound

end Silmaril.Compile.Core.Verified.Fragments
