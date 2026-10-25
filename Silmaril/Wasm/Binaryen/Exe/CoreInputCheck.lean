module

public import Silmaril.Wasm.Binaryen.Exe.Decode
public import Silmaril.Wasm.Binaryen.Exe.Encode

@[expose] public section

/-! # Additional original-input certification for the legacy byte drivers

A successful existing round trip keeps its original fast path. Otherwise the
proved Core decoder can certify alternate binary forms. Comparing two successful
canonical encodings is a conservative structural comparison: the binary grammar
is functional, so equal encoded bytes imply equality of every retained module
field. This checker adds neither a parser trust assumption nor a restriction on
which instruction constructors can be compared.

The correctness proofs are separate in `CoreInputCheckSound`. `RoundTrip`,
`checkRoundTrip` and `decodeChecked` retain their existing definitions and APIs.
-/

namespace Silmaril.Wasm.Binaryen.Exe

/-- Sound module comparison through the existing certified canonical encoder.
Failure to encode either operand yields `false`; no completeness is claimed. -/
def canonicalModuleEq (left right : Module) : Bool :=
  match encodeModule? left, encodeModule? right with
  | .ok leftBytes, .ok rightBytes => leftBytes == rightBytes
  | _, _ => false

/-- Check the actual original input with the Core decoder, then compare its
entire decoded module with the legacy frontend's candidate. -/
def checkCoreInput (input : ByteArray) (candidate : Module) : Bool :=
  match Binary.Core.Decode.decodeModule input with
  | .error _ => false
  | .ok decoded => canonicalModuleEq candidate decoded

/-- Preserve the old successful roundtrip path before attempting a Core check.
The drivers skip this fallback when blind decoder trust was explicitly chosen. -/
def inputCertified (input : ByteArray) (candidate : Module) (roundTrip : RoundTrip) : Bool :=
  if roundTrip.trusted then true else checkCoreInput input candidate

/-- Compute only certificates actually checked under the chosen trust policy.
Explicit blind trust preserves the old roundtrip report and skips Core decoding. -/
def inputCertificateFor (trustDecoder : Bool) (input : ByteArray) (candidate : Module)
    (roundTrip : RoundTrip) : Bool :=
  if trustDecoder then roundTrip.trusted else inputCertified input candidate roundTrip

end Silmaril.Wasm.Binaryen.Exe
