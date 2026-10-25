module

public import Silmaril.Wasm.Binary.Extensions.AtomicMemory.Modules
public import Silmaril.Wasm.Binary.Extensions.AtomicMemory.DecodeInstructions
public import Silmaril.Wasm.Binary.Extensions.Structured.DecodeModule

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.AtomicMemory.Decode

def decodeModule := Structured.DecodeModule.decodeModule readExpr dataIdxs

end Silmaril.Wasm.Binary.Extensions.AtomicMemory.Decode
