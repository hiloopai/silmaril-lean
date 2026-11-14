module

public import Silmaril.Compiler.Passes.Canonical.Defs
public import Silmaril.Compiler.Passes.Thms
@[expose] public section
namespace Silmaril.Compiler.Passes

/-- The reusable canonical pass runs precisely the driver's optimization stage. -/
theorem canonical_run : canonical.run = Silmaril.Compile.Registry.Stage.mirOpt := rfl

end Silmaril.Compiler.Passes
