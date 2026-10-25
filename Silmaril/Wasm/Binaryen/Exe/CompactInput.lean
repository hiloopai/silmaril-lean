module

public import Silmaril.Wasm.Binary.Core.CompactImportsDecode
public import Silmaril.Wasm.Binaryen.Exe.ProfileCleanup

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe.CompactInput

/-- Ordinary bytes for the same complete source module. Standard inputs retain
original bytes; compact inputs are expanded and encoded with the standard encoder. -/
structure Prepared where
  source : Module
  bytes : ByteArray
  normalized : Bool

/-- Keep the existing standard frontend as the fast path. The fallback only
changes binary import grouping; the complete decoded source module is retained. -/
def prepare (input : ByteArray) : Except String Prepared := do
  match Binary.Core.Decode.decodeModule input with
  | .ok source => pure ⟨source, input, false⟩
  | .error _ =>
    let source ← Binary.Core.CompactImports.Decode.decodeModule input
    let encoded ← encodeModule? source
    pure ⟨source, ⟨encoded.toArray⟩, true⟩

/-- Run an existing selected byte pipeline after the additive input boundary.
Pass selection, policies, validation and all stage guards remain in the driver. -/
def optimizeUsing (driver : ByteArray → Except String ProfileCleanupArtifact)
    (input : ByteArray) : Except String ProfileCleanupArtifact := do
  let prepared ← prepare input
  driver prepared.bytes

end Silmaril.Wasm.Binaryen.Exe.CompactInput
