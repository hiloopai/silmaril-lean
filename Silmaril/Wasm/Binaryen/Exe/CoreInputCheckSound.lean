module

public import Silmaril.Wasm.Binaryen.Exe.CoreInputCheck
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Binary.Core.DecodeSound

@[expose] public section

/-! # Certifying original input bytes after a legacy roundtrip mismatch

The syntax comparison is deliberately conditional on successful canonical
encoding. Equal certified encodings identify the same Core module by grammar
functionality, including constructors outside the legacy folding comparison.
The sound Core decoder then supplies an encoding witness for the original
input bytes, without treating canonical re-encoding as their byte identity.
-/

namespace Silmaril.Wasm.Binaryen.Exe

/-- Equal successful canonical encodings imply equality of the entire modules. -/
theorem canonicalModuleEq_sound {m n : Module}
    (equal : canonicalModuleEq m n = true) : m = n := by
  cases encodedM : encodeModule? m with
  | error error => simp [canonicalModuleEq, encodedM] at equal
  | ok bytes =>
    cases encodedN : encodeModule? n with
    | error error => simp [canonicalModuleEq, encodedM, encodedN] at equal
    | ok bytes' =>
      have sameBytes : bytes = bytes' := by
        simpa [canonicalModuleEq, encodedM, encodedN] using equal
      subst bytes'
      exact Binary.Core.functional (encodeModule?_sound encodedM)
        (encodeModule?_sound encodedN)

/-- Distinct modules can never pass the syntax comparison, whether or not
both canonical encodings exist. -/
theorem canonicalModuleEq_false_of_ne {m n : Module} (different : m ≠ n) :
    canonicalModuleEq m n = false := by
  cases compared : canonicalModuleEq m n with
  | false => rfl
  | true => exact (different (canonicalModuleEq_sound compared)).elim

/-- The comparison recognizes reflexivity whenever canonical encoding succeeds.
No claim is made that every syntactic module is encodable. -/
theorem canonicalModuleEq_refl_of_encoded {m : Module} {bytes : List UInt8}
    (encoded : encodeModule? m = .ok bytes) : canonicalModuleEq m m = true := by
  simp [canonicalModuleEq, encoded]

/-- Successful fallback certification identifies the legacy module with the
module encoded by the actual original input bytes. -/
theorem checkCoreInput_sound {input : ByteArray} {m : Module}
    (certified : checkCoreInput input m = true) :
    Binary.Core.Encodes input.data.toList m := by
  cases decoded : Binary.Core.Decode.decodeModule input with
  | error error => simp [checkCoreInput, decoded] at certified
  | ok n =>
    have sameModule : m = n := canonicalModuleEq_sound (by
      simpa [checkCoreInput, decoded] using certified)
    rw [sameModule]
    exact Binary.Core.Decode.decodeModule_sound decoded

/-- A legacy candidate differing from the certified decoding is rejected. -/
theorem checkCoreInput_false_of_decode_ne {input : ByteArray} {m n : Module}
    (decoded : Binary.Core.Decode.decodeModule input = .ok n) (different : m ≠ n) :
    checkCoreInput input m = false := by
  simpa [checkCoreInput, decoded] using canonicalModuleEq_false_of_ne different

/-- A successfully decoded, canonically encodable input is recognized even
when its original bytes use a noncanonical representation. -/
theorem checkCoreInput_of_decode {input : ByteArray} {m : Module} {bytes : List UInt8}
    (decoded : Binary.Core.Decode.decodeModule input = .ok m)
    (encoded : encodeModule? m = .ok bytes) : checkCoreInput input m = true := by
  simp [checkCoreInput, decoded, canonicalModuleEq, encoded]

end Silmaril.Wasm.Binaryen.Exe
