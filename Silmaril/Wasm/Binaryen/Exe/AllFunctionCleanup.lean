module

public import Silmaril.Wasm.Binaryen.Exe.Pipeline

@[expose] public section

/-! The fifteen existing default function stages in their shared registry
order, followed by the existing RUME stage. All executable output guards and
per-transform applicability tests are retained. This module contains runtime
definitions only; its arbitrary-profile certificates live separately. -/

namespace Silmaril.Wasm.Binaryen.Exe

/-- One guarded sixteen-stage round. Inlining is a separate pipeline stage. -/
def profileCleanupAllFunctionRound (m : BModule) : BModule :=
  rumeStage.2 (functionStageIds.foldl (fun m stage => stage.run m) m)

end Silmaril.Wasm.Binaryen.Exe
