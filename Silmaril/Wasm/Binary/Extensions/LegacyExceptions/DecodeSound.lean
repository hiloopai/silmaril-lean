module

public import Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Decode
public import Silmaril.Wasm.Binary.Extensions.LegacyExceptions.DecodeInstructionsSound
public import Silmaril.Wasm.Binary.Extensions.Structured.DecodeModuleSound

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Decode

theorem decodeModule_sound {b : ByteArray} {m : Wasm.Extensions.LegacyExceptions.Module}
    (h : decodeModule b = .ok m) : Encodes b.data.toList m :=
  Structured.DecodeModule.decodeModule_sound readExpr readExpr_sound dataIdxs h

end Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Decode
