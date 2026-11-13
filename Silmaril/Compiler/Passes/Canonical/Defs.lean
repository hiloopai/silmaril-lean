module

public import Silmaril.Compiler.Passes.Defs
public import Silmaril.Compiler.Registry.Defs
/-! Optional canonical driver selection. Keeping the registry in this module
lets clients use the generic pass-composition interface without importing the
frontend, lowering and every backend registered by the driver.
-/

@[expose] public section
namespace Silmaril.Compiler.Passes

/-- The canonical driver's registered optimization order as a reusable proved
pass. Its proof concerns Mir optimization independently of frontend correctness.
-/
def canonical : MirPass :=
  pipeline "ccomp.mirOpt" Silmaril.Compile.Registry.mirPasses

end Silmaril.Compiler.Passes
