module

public import Silmaril.Wasm.Binaryen.Toolkit.CtorEvalFallback
public import Silmaril.Wasm.Binaryen.Toolkit.CtorEvalBytesSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.CtorEval

open Execution.Core Numerics Validation
open Exe (bind_ok)

variable {H : Type}

/-- Every successful compatibility result retains exact byte meanings, validity,
actual all-profile export correctness and the existing shared Pass result.
Skipped input is byte-for-byte unchanged; it is never reported as evaluated. -/
theorem evaluateBytesOrKeep_sound {input : ByteArray} {artifact : CheckedArtifact}
    (accepted : evaluateBytesOrKeep input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧ ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧ ModuleValid artifact.result ∧
    Modes.ExportCorrect .equivalence P (closedHost (H := H)) artifact.source artifact.result ∧
    (equivalenceP (H := H) P).run artifact.source = artifact.result ∧
    (artifact.transformed = false → artifact.bytes = input ∧ artifact.result = artifact.source) ∧
    (artifact.transformed = true → recognize? artifact.source ≠ none) := by
  unfold evaluateBytesOrKeep at accepted
  cases decoded : Binary.Core.Decode.decodeModule input with
  | error e => simp [decoded, Except.mapError, bind, Except.bind] at accepted
  | ok source =>
    simp only [decoded, Except.mapError, Except.bind, bind] at accepted
    cases validated : validate? source with
    | none => simp [validated] at accepted
    | some mt =>
      simp only [validated] at accepted
      cases recognized : recognize? source with
      | none =>
        simp only [recognized] at accepted
        cases Except.ok.inj accepted
        have bytes := Binary.Core.Decode.decodeModule_sound decoded
        refine ⟨bytes, ⟨mt, validate?_sound validated⟩, bytes,
          ⟨mt, validate?_sound validated⟩, .refl _ _ _ _, ?_, by simp, by simp⟩
        change optimize source = source
        simp only [optimize, recognized]
      | some p =>
        simp only [recognized] at accepted
        obtain ⟨bytes, encoded, accepted⟩ := bind_ok accepted
        cases Except.ok.inj accepted
        have evaluated : evaluate source = .ok (mod p.type p.initial p.value true) := by
          simp only [evaluate, recognized]
        have hs := evaluate_sound (H := H) evaluated P
        refine ⟨Binary.Core.Decode.decodeModule_sound decoded, ⟨mt, validate?_sound validated⟩,
          ?_, hs.1, hs.2, evaluate_eq_pass_run (H := H) evaluated P, by simp, ?_⟩
        · simpa using Exe.encodeModule?_sound encoded
        · simp [recognized]

/-- Unsupported, accepted source syntax has a constructive unchanged result;
neither semantic equivalence nor byte preservation is merely vacuous. -/
theorem evaluateBytesOrKeep_of_unrecognized {input : ByteArray} {source : Module}
    (decoded : Binary.Core.Decode.decodeModule input = .ok source)
    {mt : CModuleType} (validated : validate? source = some mt)
    (unrecognized : recognize? source = none) :
    evaluateBytesOrKeep input = .ok ⟨⟨source, source, input⟩, false⟩ := by
  simp [evaluateBytesOrKeep, decoded, validated, unrecognized, Except.mapError, Except.bind, bind,
    pure, Except.pure]

end Silmaril.Wasm.Binaryen.Toolkit.CtorEval
