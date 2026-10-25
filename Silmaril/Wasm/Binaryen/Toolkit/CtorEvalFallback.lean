module

public import Silmaril.Wasm.Binaryen.Toolkit.CtorEvalRuntime

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.CtorEval

/-- The compatibility result distinguishes actual constructor serialization from
an unchanged, validated source. Existing `Artifact` and the rejecting tool API
remain unchanged. -/
structure CheckedArtifact extends Artifact where
  transformed : Bool

/-- A checked total transformation on the decoder/validator's accepted modules.
An unsupported constructor shape keeps the **original bytes**, without routing
through the output encoder. Malformed or invalid inputs still reject. -/
def evaluateBytesOrKeep (input : ByteArray) : Except String CheckedArtifact := do
  let source ← (Binary.Core.Decode.decodeModule input).mapError ("ctor-eval: " ++ ·)
  match Validation.validate? source with
  | none => .error "ctor-eval: module validation failed"
  | some _ =>
    match recognize? source with
    | none => pure ⟨⟨source, source, input⟩, false⟩
    | some p =>
      let result := mod p.type p.initial p.value true
      let bytes ← Exe.encodeModule? result
      pure ⟨⟨source, result, ⟨bytes.toArray⟩⟩, true⟩

def CheckedArtifact.report (artifact : CheckedArtifact) : String :=
  if artifact.transformed then "ctor-eval: transformed scalar constructor"
  else "ctor-eval: skipped unsupported constructor shape; kept original bytes"

end Silmaril.Wasm.Binaryen.Toolkit.CtorEval
