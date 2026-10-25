module

public import Silmaril.Wasm.Binary.Extensions.BinaryenMemory.Modules
public import Silmaril.Wasm.Binary.Extensions.BinaryenMemory.DecodeInstructions
public import Silmaril.Wasm.Binary.Extensions.Structured.DecodeModule

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.BinaryenMemory.Decode

def decodeModule := Structured.DecodeModule.decodeModule readExpr dataIdxs

end Silmaril.Wasm.Binary.Extensions.BinaryenMemory.Decode
