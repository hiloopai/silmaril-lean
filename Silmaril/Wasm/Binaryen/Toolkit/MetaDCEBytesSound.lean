module

public import Silmaril.Wasm.Binaryen.Toolkit.MetaDCEPass
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.MetaDCE

open Execution.Core Numerics Validation
open Exe (bind_ok)

/-- Successful serialized metadce preserves original-source admission,
initialization and arbitrary shared-store sessions at every same profile and
host-state type under the closed host, when
each requested export is selected by a graph-reachable node. Input and output
bytes denote the retained modules under the specification binary grammar.
Native compilation and filesystem IO remain separate boundaries. -/
theorem eliminateBytes_sound_hostState {H : Type} {text : String} {input : ByteArray}
    {artifact : Artifact}
    (accepted : eliminateBytes text input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧ ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧ ModuleValid artifact.result ∧
    (∀ name, name ∈ selected artifact.graph artifact.live ↔
      ∃ n ∈ artifact.graph, Reachable artifact.graph n.name ∧ n.exportName = some name) ∧
    Modes.ExportCorrectOn (· ∈ selected artifact.graph artifact.live) P
      (closedHost (H := H)) artifact.source artifact.result ∧
    (equivalenceP (H := H) (selected artifact.graph artifact.live) P).run artifact.source =
      artifact.result := by
  unfold eliminateBytes at accepted
  obtain ⟨graph, parsed, accepted⟩ := bind_ok accepted
  cases solved : solve graph with
  | none => simp only [solved] at accepted; cases accepted
  | some live =>
    simp only [solved] at accepted
    dsimp only [pure, Except.pure, throw, throwThe, Except.bind, bind] at accepted
    cases decoded : Binary.Core.Decode.decodeModule input with
    | error e => simp only [decoded, Except.mapError] at accepted; cases accepted
    | ok source =>
      simp only [decoded, Except.mapError] at accepted
      cases validated : validate? source with
      | none => simp only [validated] at accepted; cases accepted
      | some mt =>
        simp only [validated] at accepted
        by_cases hs : supported source = true
        · simp only [hs, ite_true] at accepted
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          cases validP : validate? (project (selected graph live) source) with
          | none => simp only [validP] at accepted; cases accepted
          | some mtP =>
            simp only [validP] at accepted
            cases validR : validate? (rume (tree (project (selected graph live) source))).lower with
            | none => simp only [validR] at accepted; cases accepted
            | some mtR =>
              simp only [validR] at accepted
              obtain ⟨bytes, encoded, accepted⟩ := bind_ok accepted
              cases Except.ok.inj accepted
              refine ⟨Binary.Core.Decode.decodeModule_sound decoded, ⟨mt, validate?_sound validated⟩,
                ?_, ⟨mtR, validate?_sound validR⟩, selected_iff_reachable solved,
                pipeline_correct hs ⟨mt, validate?_sound validated⟩ ⟨mtP, validate?_sound validP⟩ P, ?_⟩
              · simpa using Exe.encodeModule?_sound encoded
              · change optimize (selected graph live) source = _
                simp only [optimize, hs, ite_true, validP]
        · simp only [hs] at accepted
          cases accepted

/-- Retained empty-host-state specialization of the serialized metadce theorem. -/
theorem eliminateBytes_sound {text : String} {input : ByteArray} {artifact : Artifact}
    (accepted : eliminateBytes text input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧ ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧ ModuleValid artifact.result ∧
    (∀ name, name ∈ selected artifact.graph artifact.live ↔
      ∃ n ∈ artifact.graph, Reachable artifact.graph n.name ∧ n.exportName = some name) ∧
    Modes.ExportCorrectOn (· ∈ selected artifact.graph artifact.live) P
      (closedHost (H := Empty)) artifact.source artifact.result ∧
    (equivalenceP (H := Empty) (selected artifact.graph artifact.live) P).run artifact.source =
      artifact.result :=
  eliminateBytes_sound_hostState accepted P

end Silmaril.Wasm.Binaryen.Toolkit.MetaDCE
