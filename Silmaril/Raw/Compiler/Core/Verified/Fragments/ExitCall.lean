module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.ExitCall.Defs
/-! # Fragment: `main` starts with `exit(e)`, `e` a closed integer expression

The folded argument is returned from `__ccomp_start`, which crt0 observes as `exit` does. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- `ExitCall.recognize`'s folded argument, returned by `ConstLink.link`. -/
def exitCall : Fragment := .ofConst ExitCall.recognize ExitCall.recognize_sound

end Silmaril.Compile.Core.Verified.Fragments
