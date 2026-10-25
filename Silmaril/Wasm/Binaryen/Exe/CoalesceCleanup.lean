module

public import Silmaril.Wasm.Binaryen.Exe.ProfileCleanup

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

/-- The original twelve-stage round followed by the unchanged overwrite-anchored
dead-store transform. Runtime-only: do not import its proof packager here. -/
def profileCleanupCoalesceRound (m : BModule) : BModule :=
  CoalesceLocalsLite.deadSetLite (profileCleanupRound m)

/-- Thirteen-stage rounds through the same checked byte boundary. The old
twelve-stage byte API and its outputs remain unchanged. -/
def cleanupCoalesceBytes (rounds : Nat) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  cleanupTransformBytes (profileCleanupCoalesceRound^[rounds]) input

end Silmaril.Wasm.Binaryen.Exe
