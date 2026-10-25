module

public import Silmaril.Wasm.Binary.Core.Decode

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- The specification decoder with the caller's input label retained in errors. -/
def decodeInput (side : String) (bytes : ByteArray) : Except String Wasm.Module :=
  (Binary.Core.Decode.decodeModule bytes).mapError (fun e => side ++ ": " ++ e)

end Silmaril.Wasm.Binaryen.Toolkit
