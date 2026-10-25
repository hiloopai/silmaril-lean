module

public import Silmaril.Wasm.Binaryen.Toolkit.ExperimentalPreparedMerge
public import Silmaril.Wasm.Binaryen.Toolkit.ExperimentalExportMergeSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Original bytes, both actual preparation stages, checked linking, the public
interface recipe and valid encoded output. No interface-transport or full
execution-equivalence theorem is smuggled into this structural contract. -/
theorem experimentalPreparedMergeBytes_sound
    {policy : MergeExportNames.Policy} {inputs : List (String × ByteArray)}
    {artifact : PreparedMergedArtifact}
    (accepted : experimentalPreparedMergeBytes policy inputs = .ok artifact) :
    List.Forall₂ (fun input decoded => input.1 = decoded.1 ∧
      Binary.Core.Encodes input.2.data.toList decoded.2) inputs artifact.inputs ∧
    eraseSilentStarts artifact.inputs = .ok artifact.startless ∧
    MergeExportNames.prepare? policy artifact.startless = some artifact.prepared ∧
    checkedMerge? artifact.prepared.modules = some artifact.linked ∧
    artifact.merged = MergeExportNames.publicModule policy artifact.prepared.aliases artifact.linked ∧
    Validation.ModuleValid artifact.merged ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.merged := by
  unfold experimentalPreparedMergeBytes at accepted
  obtain ⟨modules, decoded, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨startless, starts, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨prepared, preparation, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨linked, linking, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨merged, checked, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨bytes, encoded, accepted⟩ := Exe.bind_ok accepted
  cases Except.ok.inj accepted
  have preparedEq : MergeExportNames.prepare? policy startless = some prepared := by
    unfold prepareExportMergeModules at preparation
    split at preparation
    · cases preparation
    · cases preparation
      assumption
  have linkedEq : checkedMerge? prepared.modules = some linked := by
    unfold mergeModules at linking
    split at linking
    · cases linking
      assumption
    · cases linking
  have checkedEq : Link.GC.validated?
      (MergeExportNames.publicModule policy prepared.aliases linked) = some merged := by
    unfold validateExportMergePublic at checked
    split at checked
    · cases checked
    · cases checked
      assumption
  have outputEq : merged = MergeExportNames.publicModule policy prepared.aliases linked := by
    unfold Link.GC.validated? at checkedEq
    split at checkedEq
    · exact Option.some.inj checkedEq.symm
    · cases checkedEq
  exact ⟨decodeMergeInputs_sound decoded, starts, preparedEq, linkedEq, outputEq,
    Link.GC.validated?_sound checkedEq, Exe.encodeModule?_sound encoded⟩

end Silmaril.Wasm.Binaryen.Toolkit
