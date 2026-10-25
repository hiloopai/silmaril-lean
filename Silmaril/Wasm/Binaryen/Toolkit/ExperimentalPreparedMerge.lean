module

public import Silmaril.Wasm.Binaryen.Toolkit.ExperimentalExportMerge
public import Silmaril.Wasm.Binaryen.Toolkit.SilentStartMerge

@[expose] public section

/-! Combine the two additive preparation stages without discarding provenance.
Original-interface semantic equivalence still requires alias observation-name
transport; successful output validation alone does not supply that theorem.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

structure PreparedMergedArtifact where
  inputs : List (String × Wasm.Module)
  startless : List (String × Wasm.Module)
  prepared : Binaryen.MergeExportNames.Prepared
  linked : Wasm.Module
  merged : Wasm.Module
  bytes : ByteArray

def experimentalPreparedMergeBytes (policy : Binaryen.MergeExportNames.Policy)
    (inputs : List (String × ByteArray)) : Except String PreparedMergedArtifact := do
  let modules ← decodeMergeInputs inputs
  let startless ← eraseSilentStarts modules
  let prepared ← prepareExportMergeModules policy startless
  let linked ← mergeModules prepared.modules
  let merged ← validateExportMergePublic policy prepared.aliases linked
  let bytes ← Exe.encodeModule? merged
  pure ⟨modules, startless, prepared, linked, merged, ⟨bytes.toArray⟩⟩

end Silmaril.Wasm.Binaryen.Toolkit
