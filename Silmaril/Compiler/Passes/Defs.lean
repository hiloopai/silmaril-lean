module

public import Silmaril.Compiler.Mir.Pass.Defs
/-! Composable private compiler passes. Each Mir pass carries its refinement
proof against the independent Mir semantics. A pipeline is another pass, so
clients can select, reorder and nest proved passes without changing the driver
or manufacturing a fresh correctness assumption. This interface does not identify
the canonical C lowering with the separately frozen csem validator lowering.
-/

@[expose] public section
namespace Silmaril.Compiler.Passes

abbrev MirPass := Silmaril.Compile.Mir.Pass

/-- Package any ordered selection of proved transformations as one reusable pass. -/
def pipeline (name : String) (passes : List MirPass) : MirPass where
  name := name
  run := Silmaril.Compile.Mir.Pass.runAll passes
  correct := Silmaril.Compile.Mir.Pass.runAll_correct passes

end Silmaril.Compiler.Passes
