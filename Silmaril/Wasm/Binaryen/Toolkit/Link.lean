module

public import Silmaril.Wasm.Binaryen.Toolkit.ByteInput
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Link.GC

/-! # A byte-input API for the partial GC linker

Use the specification decoder, the existing validated two-module linker, and
the certified encoder. The successful result retains the actual source and
linked modules so that execution theorems can use the existing linking recipe.
No optimizer profile or untrusted-decoder option is involved.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

structure LinkedArtifact where
  provider : Wasm.Module
  consumer : Wasm.Module
  linked : Wasm.Module
  bytes : ByteArray

def linkModules (namespaceName : String) (provider consumer : Wasm.Module) :
    Except String Wasm.Module :=
  match Link.GC.link? namespaceName provider consumer with
  | some linked => .ok linked
  | none => .error "link-gc: unsupported profile, invalid module, unresolved import, signature mismatch, duplicate export, or index overflow"

/-- The provider is import-free. The consumer imports only provider functions
under `namespaceName`. Both modules have no memories, tables, tags, segments,
or start functions; supported functions, globals and GC types are relocated.
Unsupported input or output encoding returns an error, never a partial result. -/
def linkBytes (namespaceName : String) (providerBytes consumerBytes : ByteArray) :
    Except String LinkedArtifact := do
  let provider ← decodeInput "provider" providerBytes
  let consumer ← decodeInput "consumer" consumerBytes
  let linked ← linkModules namespaceName provider consumer
  let bytes ← Exe.encodeModule providerBytes linked
  pure ⟨provider, consumer, linked, bytes⟩

end Silmaril.Wasm.Binaryen.Toolkit
