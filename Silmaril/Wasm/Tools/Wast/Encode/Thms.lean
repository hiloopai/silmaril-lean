module

public import Silmaril.Wasm.Tools.Wast.Encode.Defs
public import Silmaril.Wasm.Tools.Text.Thms
public import Silmaril.Wasm.Tools.Layout.Thms
import Silmaril.Proofs.Wasm.Tools.Wast.Encode

/-!
# The checked text encoder is sound on the certified fragment

`checkedCore_sound`: when the certified pipeline reads the text `src` to a module `m`
(`Text.textTree?`, so that the annotation-stripped text encodes `m` in the SpecTec text
grammar, `Text.textTree?_sound`) and the certified encoder encodes `m`, whatever
`checkedCore` returns encodes, in the binary grammar, a module equal to `m` up to the type of
function-index element segments (`normElems`), whichever bytes the unverified transcription
proposed. `acceptsNorm_sound` is the check behind the "up to". Proofs in
`Silmaril.Proofs.Wasm.Tools.Wast.Encode`. `checkedCore_spec` combines
both grammars.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril Silmaril.Wasm

theorem checkedCore_sound {src : String} {cand : Except String ByteArray} {b : ByteArray}
    {x : Text.SExp} {m : Wasm.Module} {canon : List UInt8} (ht : Text.textTree? src = .ok (x, m))
    (hcanon : Binaryen.Exe.encodeModuleWith? (Binaryen.Exe.usesDataIdx m) m = .ok canon)
    (h : checkedCore src cand = .ok b) :
    ∃ m', Binary.Core.Encodes b.data.toList m' ∧ normElems m' = normElems m :=
  checkedCore_sound_raw ht hcanon h

/-- The specification of the checked encoder on the certified fragment: the text encodes `m`
in the formal text grammar, and the output bytes encode, in the formal binary grammar, a
module equal to `m` up to the type of function-index element segments. -/
theorem checkedCore_spec {src : String} {cand : Except String ByteArray} {b : ByteArray}
    {x : Text.SExp} {m : Wasm.Module} {canon : List UInt8} (ht : Text.textTree? src = .ok (x, m))
    (hcanon : Binaryen.Exe.encodeModuleWith? (Binaryen.Exe.usesDataIdx m) m = .ok canon)
    (h : checkedCore src cand = .ok b) :
    Text.Core.Encodes (Annot.stripTrivia src) m ∧
      ∃ m', Binary.Core.Encodes b.data.toList m' ∧ normElems m' = normElems m :=
  ⟨Text.textTree?_sound ht, checkedCore_sound ht hcanon h⟩

end Silmaril.Wasm.Tools.Wast
