module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.ReturnSound.Defs
/-! # Fragment: `main` returns a closed pure integer expression

The expression is constant-folded by `Fold.eval` (`Return.recognize`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- `Return.recognize`'s folded integer, returned by `ConstLink.link`. -/
def returnFold : Fragment := .ofConst Return.recognize Return.recognize_sound

end Silmaril.Compile.Core.Verified.Fragments
