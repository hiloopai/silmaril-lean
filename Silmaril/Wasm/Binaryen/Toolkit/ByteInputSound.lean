module

public import Silmaril.Wasm.Binaryen.Toolkit.ByteInput
public import Silmaril.Wasm.Binary.Core.DecodeSound

/-! Specification guarantee for the shared byte decoder, independent of the
linker and its semantic proofs. The original theorem name is preserved. -/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

theorem decodeInput_sound {side : String} {bytes : ByteArray} {m : Wasm.Module}
    (h : decodeInput side bytes = .ok m) : Binary.Core.Encodes bytes.data.toList m := by
  cases decoded : Binary.Core.Decode.decodeModule bytes with
  | error e => simp [decodeInput, decoded, Except.mapError] at h
  | ok result =>
      simp [decodeInput, decoded, Except.mapError] at h
      cases h
      exact Binary.Core.Decode.decodeModule_sound decoded

end Silmaril.Wasm.Binaryen.Toolkit
