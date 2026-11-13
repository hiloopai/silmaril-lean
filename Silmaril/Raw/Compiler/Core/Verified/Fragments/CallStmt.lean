module

public import Silmaril.Compiler.Core.Verified.Fragments.Call.Defs
/-! # Fragment: `g(); return e;`, where `g` has no parameters. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- `g(); return e;`, where `g` has no parameters. -/
def callStmt : Fragment := callFragment 1

end Silmaril.Compile.Core.Verified.Fragments
