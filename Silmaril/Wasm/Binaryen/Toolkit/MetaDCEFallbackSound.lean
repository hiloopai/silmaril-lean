module

public import Silmaril.Wasm.Binaryen.Toolkit.MetaDCEFallback
public import Silmaril.Wasm.Binaryen.Toolkit.MetaDCEBytesSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.MetaDCE

open Execution.Core Numerics Validation
open Exe (bind_ok)

/-- The compatibility path preserves exact original bytes on skipped shapes,
while retaining the same actual original-source, selected-interface correctness
and shared Pass result at every profile and host-state type under the closed host.
Graph parse/binding errors still reject. -/
theorem eliminateBytesOrKeep_sound_hostState {H : Type} {text : String} {input : ByteArray}
    {artifact : CheckedArtifact}
    (accepted : eliminateBytesOrKeep text input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧ ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧ ModuleValid artifact.result ∧
    (∀ name, name ∈ selected artifact.graph artifact.live ↔
      ∃ n ∈ artifact.graph, Reachable artifact.graph n.name ∧ n.exportName = some name) ∧
    Modes.ExportCorrectOn (· ∈ selected artifact.graph artifact.live) P
      (closedHost (H := H)) artifact.source artifact.result ∧
    (equivalenceP (H := H) (selected artifact.graph artifact.live) P).run artifact.source =
      artifact.result ∧
    (artifact.transformed = false → artifact.bytes = input ∧ artifact.result = artifact.source) := by
  unfold eliminateBytesOrKeep at accepted
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
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        by_cases hs : supported source = true
        · simp only [hs, ite_true] at accepted
          obtain ⟨result, checked, accepted⟩ := bind_ok accepted
          cases Except.ok.inj accepted
          obtain ⟨hi, hv, ho, hr, hg, hc, hp⟩ := eliminateBytes_sound_hostState (H := H) checked P
          exact ⟨hi, hv, ho, hr, hg, hc, hp, by simp⟩
        · simp only [hs] at accepted
          cases Except.ok.inj accepted
          have bytes := Binary.Core.Decode.decodeModule_sound decoded
          refine ⟨bytes, ⟨mt, validate?_sound validated⟩, bytes, ⟨mt, validate?_sound validated⟩,
            selected_iff_reachable solved, .refl _ _ _ _, ?_, by simp⟩
          change optimize (selected graph live) source = source
          simp [optimize, hs]

/-- Retained empty-host-state specialization of the compatibility endpoint. -/
theorem eliminateBytesOrKeep_sound {text : String} {input : ByteArray} {artifact : CheckedArtifact}
    (accepted : eliminateBytesOrKeep text input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧ ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧ ModuleValid artifact.result ∧
    (∀ name, name ∈ selected artifact.graph artifact.live ↔
      ∃ n ∈ artifact.graph, Reachable artifact.graph n.name ∧ n.exportName = some name) ∧
    Modes.ExportCorrectOn (· ∈ selected artifact.graph artifact.live) P
      (closedHost (H := Empty)) artifact.source artifact.result ∧
    (equivalenceP (H := Empty) (selected artifact.graph artifact.live) P).run artifact.source =
      artifact.result ∧
    (artifact.transformed = false → artifact.bytes = input ∧ artifact.result = artifact.source) :=
  eliminateBytesOrKeep_sound_hostState accepted P

theorem eliminateBytesOrKeep_of_unsupported {text : String} {input : ByteArray}
    {graph : Graph} {live : List String} {source : Module} {mt : CModuleType}
    (parsed : parseGraph text = .ok graph) (solved : solve graph = some live)
    (decoded : Binary.Core.Decode.decodeModule input = .ok source)
    (validated : validate? source = some mt) (bound : checkBindings graph source = .ok ())
    (unsupported : supported source = false) :
    eliminateBytesOrKeep text input = .ok ⟨⟨graph, live, source, source, source, input⟩, false⟩ := by
  simp [eliminateBytesOrKeep, parsed, solved, decoded, validated, bound, unsupported,
    Except.mapError, Except.bind, bind, pure, Except.pure]

end Silmaril.Wasm.Binaryen.Toolkit.MetaDCE
