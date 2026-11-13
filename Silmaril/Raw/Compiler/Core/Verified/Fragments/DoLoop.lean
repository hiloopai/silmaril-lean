module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.DoMainSound.Defs
/-! # Fragment: one `do` loop over integer locals

The body executes before testing, including when the first test is false.
The generated graph has a real back edge, with all values computed at runtime.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- Body-first saved-label loop, with the productive macro-step proof. -/
def doLoop : Fragment where
  compile := DoMain.compile
  sound := DoMain.compile_sound

end Silmaril.Compile.Core.Verified.Fragments
