module

public import Silmaril.Wasm.Binaryen.MergeChecked
public import Silmaril.Wasm.Binaryen.Toolkit.Link

@[expose] public section

/-! # Byte-input in-order GC merge

Named inputs keep their original namespaces for the graph check. Successful
output records every decoded source module and the actual checked merge; no
memory/table/start fallback or general `wasm-merge` alias is introduced.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

structure MergedArtifact where
  inputs : List (String × Wasm.Module)
  merged : Wasm.Module
  bytes : ByteArray

def decodeMergeInputs : List (String × ByteArray) → Except String (List (String × Wasm.Module))
  | [] => .ok []
  | (name, bytes) :: rest => do
      let m ← decodeInput name bytes
      let modules ← decodeMergeInputs rest
      pure ((name, m) :: modules)

def mergeModules (modules : List (String × Wasm.Module)) : Except String Wasm.Module :=
  match checkedMerge? modules with
  | some merged => .ok merged
  | none => .error "merge-gc: unsupported profile, invalid module, empty input, duplicate namespace/export, non-backward or unresolved import, signature mismatch, or index overflow"

/-- N-ary, namespace-sensitive, in-order GC linking with certified binary I/O.
The first module is import-free; every later import must name an export in an
earlier named module. All modules have the same memory/table/start-free profile
as `link-gc`. Singleton input is validated, and empty input is rejected. -/
def mergeBytes (inputs : List (String × ByteArray)) : Except String MergedArtifact := do
  let modules ← decodeMergeInputs inputs
  let merged ← mergeModules modules
  let bytes ← Exe.encodeModule? merged
  pure ⟨modules, merged, ⟨bytes.toArray⟩⟩

end Silmaril.Wasm.Binaryen.Toolkit
