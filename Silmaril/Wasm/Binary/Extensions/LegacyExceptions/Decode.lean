module

public import Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Modules
public import Silmaril.Wasm.Binary.Extensions.LegacyExceptions.DecodeInstructions
public import Silmaril.Wasm.Binary.Extensions.Structured.DecodeModule

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Decode

def decodeModule := Structured.DecodeModule.decodeModule readExpr dataIdxs

end Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Decode
