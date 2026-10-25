module

public import Silmaril.Wasm.Binaryen.Toolkit.CtorEvalPass
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.CtorEval

open Execution.Core Numerics Validation
open Exe (bind_ok)

/-- Successful real input/output bytes denote valid retained modules with actual
admission, initialization and shared-store sessions equivalent at every same
numerical profile and host-state type under the closed host. Native compilation
and file IO are separate boundaries. -/
theorem evaluateBytes_sound_hostState {H : Type} {input : ByteArray} {artifact : Artifact}
    (accepted : evaluateBytes input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧ ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧ ModuleValid artifact.result ∧
    Modes.ExportCorrect .equivalence P (closedHost (H := H)) artifact.source artifact.result := by
  unfold evaluateBytes at accepted
  cases decoded : Binary.Core.Decode.decodeModule input with
  | error e => simp [decoded, Except.mapError, bind, Except.bind] at accepted
  | ok source =>
    simp only [decoded, Except.mapError, Except.bind, bind] at accepted
    cases validated : validate? source with
    | none => simp [validated] at accepted
    | some mt =>
      simp only [validated] at accepted
      obtain ⟨result, evaluated, accepted⟩ := bind_ok accepted
      obtain ⟨bytes, encoded, accepted⟩ := bind_ok accepted
      cases Except.ok.inj accepted
      have hs := evaluate_sound (H := H) evaluated P
      exact ⟨Binary.Core.Decode.decodeModule_sound decoded, ⟨mt, validate?_sound validated⟩,
        by simpa using Exe.encodeModule?_sound encoded, hs.1, hs.2⟩

/-- Retained empty-host-state specialization of the serialized evaluator. -/
theorem evaluateBytes_sound {input : ByteArray} {artifact : Artifact}
    (accepted : evaluateBytes input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧ ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧ ModuleValid artifact.result ∧
    Modes.ExportCorrect .equivalence P (closedHost (H := Empty)) artifact.source artifact.result :=
  evaluateBytes_sound_hostState accepted P

end Silmaril.Wasm.Binaryen.Toolkit.CtorEval
