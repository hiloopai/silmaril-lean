module

public import Silmaril.Wasm.Binaryen.Toolkit.Merge
public import Silmaril.Wasm.Link.SilentStart

@[expose] public section

/-! Additive merge preparation for finite, silent start functions.

The original decoded modules and the exact start-erased modules are retained
separately. Every original module must validate. Only the checked `SilentStart`
fragment can be erased; all other module fields remain unchanged. The original
`mergeBytes` API is unchanged. Execution equivalence requires the separate
silent-start initialization theorem in addition to the checked merger theorem.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

def eraseSilentStartModule (ns : String) (m : Wasm.Module) : Except String Wasm.Module :=
  if !(Validation.validate? m).isSome then
    .error (ns ++ ": original module validation failed before start preparation")
  else match Link.SilentStart.erase? m with
    | none => .error (ns ++ ": start is outside the checked finite silent fragment")
    | some erased => .ok erased

def eraseSilentStarts : List (String × Wasm.Module) →
    Except String (List (String × Wasm.Module))
  | [] => .ok []
  | (ns, m) :: rest => do
      let erased ← eraseSilentStartModule ns m
      let tail ← eraseSilentStarts rest
      pure ((ns, erased) :: tail)

structure SilentStartMergedArtifact where
  inputs : List (String × Wasm.Module)
  prepared : List (String × Wasm.Module)
  merged : Wasm.Module
  bytes : ByteArray

def mergeSilentStartBytes (inputs : List (String × ByteArray)) :
    Except String SilentStartMergedArtifact := do
  let modules ← decodeMergeInputs inputs
  let prepared ← eraseSilentStarts modules
  let merged ← mergeModules prepared
  let bytes ← Exe.encodeModule? merged
  pure ⟨modules, prepared, merged, ⟨bytes.toArray⟩⟩

end Silmaril.Wasm.Binaryen.Toolkit
