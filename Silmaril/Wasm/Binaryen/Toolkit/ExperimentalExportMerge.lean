module

public import Silmaril.Wasm.Binaryen.Toolkit.Merge
public import Silmaril.Wasm.Binaryen.MergeExportNames

@[expose] public section

/-! Additive export-policy merging. Original decoded inputs, the exact alias map
and prepared program are retained. This endpoint certifies the actual checked
merge of the prepared program and a valid binary output; semantic equivalence
to the original interfaces requires an additional name-transport theorem. The
existing default `mergeBytes` and its execution/session contracts are unchanged.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

structure ExportMergedArtifact where
  inputs : List (String × Wasm.Module)
  prepared : Binaryen.MergeExportNames.Prepared
  linked : Wasm.Module
  merged : Wasm.Module
  bytes : ByteArray

def validateExportMergeInputs (modules : List (String × Wasm.Module)) : Except String Unit :=
  if modules.all (fun p => (Validation.validate? p.2).isSome) then .ok ()
  else .error "merge-export-names: original input module validation failed"

def prepareExportMergeModules (policy : Binaryen.MergeExportNames.Policy)
    (modules : List (String × Wasm.Module)) : Except String Binaryen.MergeExportNames.Prepared :=
  match Binaryen.MergeExportNames.prepare? policy modules with
  | none => .error "merge-export-names: could not allocate distinct export aliases"
  | some prepared => .ok prepared

def validateExportMergePublic (policy : Binaryen.MergeExportNames.Policy)
    (aliases : List Binaryen.MergeExportNames.Alias) (linked : Wasm.Module) :
    Except String Wasm.Module :=
  match Link.GC.validated? (Binaryen.MergeExportNames.publicModule policy aliases linked) with
  | none => .error "merge-export-names: final public interface failed validation"
  | some merged => .ok merged

def experimentalExportMergeBytes (policy : Binaryen.MergeExportNames.Policy)
    (inputs : List (String × ByteArray)) : Except String ExportMergedArtifact := do
  let modules ← decodeMergeInputs inputs
  let _ ← validateExportMergeInputs modules
  let prepared ← prepareExportMergeModules policy modules
  let linked ← mergeModules prepared.modules
  let merged ← validateExportMergePublic policy prepared.aliases linked
  let bytes ← Exe.encodeModule? merged
  pure ⟨modules, prepared, linked, merged, ⟨bytes.toArray⟩⟩

end Silmaril.Wasm.Binaryen.Toolkit
