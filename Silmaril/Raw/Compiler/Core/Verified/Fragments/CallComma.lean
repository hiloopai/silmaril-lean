module

public import Silmaril.Compiler.Core.Verified.Fragments.Call.Defs
/-! # Fragment: `return g(), e;`, where `g` has no parameters. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- `return g(), e;`, where `g` has no parameters. -/
def callComma : Fragment := callFragment 2

end Silmaril.Compile.Core.Verified.Fragments
