module

public import Silmaril.Wasm.Binaryen.Exe.AllFunctionCleanup
public import Silmaril.Wasm.Binaryen.Exe.TrapGrowCleanup

@[expose] public section

/-! Byte and policy entry points for the complete existing function-stage registry.
This runtime module imports no arbitrary-profile proof packagers. Inlining is
separate; all per-transform checks and the registered output guards remain active.
-/

namespace Silmaril.Wasm.Binaryen.Exe

/-- All fifteen guarded function transformations, followed by guarded RUME,
through the existing verified-decoder/validator/encoder boundary. -/
def cleanupAllFunctionBytes (rounds : Nat) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  cleanupTransformBytes (profileCleanupAllFunctionRound^[rounds]) input

/-- The larger exact pipeline with the existing optional refinement rewrite. -/
def optimizeAllFunctionModeBytes (options : ModeCleanupOptions) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  optimizeModeBytesUsing cleanupAllFunctionBytes options input

/-- The larger exact pipeline with both existing policy-specific rewrites.
Their mode checks and unsupported-module fallbacks are unchanged. -/
def optimizeAllFunctionTrapGrowBytes (options : TrapGrowOptions) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  optimizeTrapGrowBytesUsing cleanupAllFunctionBytes options input

end Silmaril.Wasm.Binaryen.Exe
