module

public import Silmaril.Wasm.Binaryen.Toolkit.Merge
public import Silmaril.Wasm.Binaryen.Exe.CoreInputCheck

@[expose] public section

/-! Exact byte-preserving identities for arbitrary admitted closed modules.
The empty module introduces no indices, allocations, effects or exports, so
there is no reason to impose the ordinary GC relocation profile on its partner.
This endpoint is deliberately separate from the existing relocation algorithm.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

inductive EmptyIdentitySide where
  | left
  | right
  deriving DecidableEq

structure EmptyIdentityMergedArtifact where
  inputs : List (String × Wasm.Module)
  survivor : String
  merged : Wasm.Module
  bytes : ByteArray
  side : EmptyIdentitySide

def validateIdentityPartner (m : Wasm.Module) : Except String Unit :=
  if !m.imports.isEmpty then .error "empty identity: partner must be import-free"
  else if !(Validation.validate? m).isSome then .error "empty identity: invalid partner"
  else .ok ()

/-- Either side may be the empty module. The other module may contain any
valid Core feature supported by the binary codec, including resource sections
and starts. Its exact original bytes are the output; nothing is re-encoded. -/
def mergeEmptyIdentityBytes (inputs : List (String × ByteArray)) :
    Except String EmptyIdentityMergedArtifact := do
  match inputs with
  | [(leftName, leftBytes), (rightName, rightBytes)] =>
      if leftName == rightName then throw "empty identity: duplicate namespace"
      let left ← decodeInput leftName leftBytes
      let right ← decodeInput rightName rightBytes
      if Exe.canonicalModuleEq left {} then
        validateIdentityPartner right
        pure ⟨[(leftName, left), (rightName, right)], rightName, right, rightBytes, .left⟩
      else if Exe.canonicalModuleEq right {} then
        validateIdentityPartner left
        pure ⟨[(leftName, left), (rightName, right)], leftName, left, leftBytes, .right⟩
      else throw "empty identity: neither module is empty"
  | _ => throw "empty identity: expected exactly two named modules"

end Silmaril.Wasm.Binaryen.Toolkit
