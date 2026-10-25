module

public import Silmaril.Wasm.Binary.Extensions.AtomicMemory.Decode
public import Silmaril.Wasm.Binary.Extensions.AtomicMemory.DecodeInstructionsSound
public import Silmaril.Wasm.Binary.Extensions.Structured.DecodeModuleSound

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.AtomicMemory.Decode

theorem decodeModule_sound {b : ByteArray} {m : Wasm.Extensions.AtomicMemory.Module}
    (h : decodeModule b = .ok m) : Encodes b.data.toList m :=
  Structured.DecodeModule.decodeModule_sound readExpr readExpr_sound dataIdxs h

end Silmaril.Wasm.Binary.Extensions.AtomicMemory.Decode
