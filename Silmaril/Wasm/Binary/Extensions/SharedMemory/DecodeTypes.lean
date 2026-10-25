module

public import Silmaril.Wasm.Binary.Extensions.SharedMemory.Types
public import Silmaril.Wasm.Binary.Core.Decode

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.SharedMemory.Decode

open Core.Decode

/-- Read ordinary or shared memory limits, retaining the original shared bit.
No Core decoder receives rewritten input bytes. -/
def readMemType : DecodeM MemoryType := do
  match (← peekByte).map UInt8.toNat with
  | some 0x03 =>
    let _ ← readByte
    let n ← readLimits.readBound 64
    let m ← readLimits.readBound 64
    pure ⟨⟨.i32, ⟨n, some m⟩⟩, true⟩
  | some 0x07 =>
    let _ ← readByte
    let n ← readLimits.readBound 64
    let m ← readLimits.readBound 64
    pure ⟨⟨.i64, ⟨n, some m⟩⟩, true⟩
  | _ => pure ⟨← Core.Decode.readMemType, false⟩

end Silmaril.Wasm.Binary.Extensions.SharedMemory.Decode
