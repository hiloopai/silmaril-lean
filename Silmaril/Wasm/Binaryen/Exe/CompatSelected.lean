module

public import Silmaril.Wasm.Binaryen.Exe.CompactInput
public import Silmaril.Wasm.Binaryen.Exe.ZeroGrowCleanup

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

/-- The selected CLI's pure byte endpoint. Standard inputs keep the original
frontend; compact import groups are certified and expanded before the same
selected pipeline. Policy selection, validation and transformations are unchanged. -/
def optimizeSelectedCompatBytes (stages : List CleanupStage) (options : TrapGrowOptions)
    (selectZeroGrowSuccess : Bool) (input : ByteArray) : Except String ProfileCleanupArtifact :=
  CompactInput.optimizeUsing
    (if selectZeroGrowSuccess then optimizeSelectedZeroGrowBytes stages options
     else optimizeSelectedTrapGrowBytes stages options) input

end Silmaril.Wasm.Binaryen.Exe
