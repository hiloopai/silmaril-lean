module

public import Silmaril.Wasm.Binaryen.Toolkit.ExperimentalExportMerge
public import Silmaril.Wasm.Binaryen.Toolkit.MergeSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

theorem validateExportMergeInputs_sound {modules : List (String × Wasm.Module)}
    {u : Unit} (accepted : validateExportMergeInputs modules = .ok u) :
    ∀ p ∈ modules, Validation.ModuleValid p.2 := by
  unfold validateExportMergeInputs at accepted
  split at accepted
  · rename_i valid
    intro p member
    exact Validation.validate?_isSome_iff.mp (List.all_eq_true.mp valid p member)
  · cases accepted

/-- Exact original-byte provenance, actual name preparation and checked linking,
the public-interface recipe, and valid encoded output. This theorem makes no
original-interface execution-equivalence claim. -/
theorem experimentalExportMergeBytes_full_sound
    {policy : MergeExportNames.Policy} {inputs : List (String × ByteArray)}
    {artifact : ExportMergedArtifact}
    (accepted : experimentalExportMergeBytes policy inputs = .ok artifact) :
    List.Forall₂ (fun input decoded => input.1 = decoded.1 ∧
      Binary.Core.Encodes input.2.data.toList decoded.2) inputs artifact.inputs ∧
    (∀ p ∈ artifact.inputs, Validation.ModuleValid p.2) ∧
    MergeExportNames.prepare? policy artifact.inputs = some artifact.prepared ∧
    checkedMerge? artifact.prepared.modules = some artifact.linked ∧
    artifact.merged = MergeExportNames.publicModule policy artifact.prepared.aliases artifact.linked ∧
    Validation.ModuleValid artifact.merged ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.merged := by
  unfold experimentalExportMergeBytes at accepted
  obtain ⟨modules, decoded, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨u, originals, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨prepared, preparation, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨linked, linking, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨merged, checked, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨bytes, encoded, accepted⟩ := Exe.bind_ok accepted
  cases Except.ok.inj accepted
  have preparedEq : MergeExportNames.prepare? policy modules = some prepared := by
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
  exact ⟨decodeMergeInputs_sound decoded, validateExportMergeInputs_sound originals,
    preparedEq, linkedEq, outputEq,
    Link.GC.validated?_sound checkedEq, Exe.encodeModule?_sound encoded⟩

/-- Preserved source-preparation and binary-output contract. -/
theorem experimentalExportMergeBytes_sound
    {policy : MergeExportNames.Policy} {inputs : List (String × ByteArray)}
    {artifact : ExportMergedArtifact}
    (accepted : experimentalExportMergeBytes policy inputs = .ok artifact) :
    List.Forall₂ (fun input decoded => input.1 = decoded.1 ∧
      Binary.Core.Encodes input.2.data.toList decoded.2) inputs artifact.inputs ∧
    MergeExportNames.prepare? policy artifact.inputs = some artifact.prepared ∧
    checkedMerge? artifact.prepared.modules = some artifact.linked ∧
    artifact.merged = MergeExportNames.publicModule policy artifact.prepared.aliases artifact.linked ∧
    Validation.ModuleValid artifact.merged ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.merged := by
  obtain ⟨originals, _, prepared⟩ := experimentalExportMergeBytes_full_sound accepted
  exact ⟨originals, prepared⟩

end Silmaril.Wasm.Binaryen.Toolkit
