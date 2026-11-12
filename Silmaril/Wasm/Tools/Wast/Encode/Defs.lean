module

public import Silmaril.Wasm.Tools.Text.Defs
public import Silmaril.Wasm.Tools.Layout.Defs

/-!
# A checked text encoder: the `wast` crate's layout, the certified module

`checkedCore src cand` is the binary of the core module text `src` that `json-from-wast` and
`wast` write, given `cand`, the bytes of the transcription of the `wast` crate's encoder
(`Silmaril.Wasm.Tools.WastEnc.encodeModule`, unverified):

* when silmaril-lean's certified pipeline reads `src` (`Text.textTree?`: the certified lexer
  and elaborator, sound for the SpecTec text grammar) to a module `m`, `cand` is returned only
  if the certified decoder reads it back to the module whose certified encoding is `m`'s
  (`Layout.accepts`); otherwise the `parse` subcommand's bytes (`Text.textToBinary`). Either
  way the result encodes `m` (`checkedCore_sound` in `…/Encode/Thms.lean`);
* when the certified pipeline does not read `src` (modules outside silmaril-lean's fragment:
  post-3.0 proposals, unbound type indices, out-of-range limits), `cand` unchecked.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril Silmaril.Wasm

/-- The function-reference type `(ref null func)` and its non-null form `(ref func)`. -/
def funcrefT : RefType := ⟨true, .abstract .func⟩
def funcNonNullT : RefType := ⟨false, .abstract .func⟩

/-- Is every item of a segment a single `ref.func` (the function-index form)? -/
def funcIndexItems (e : Elem) : Bool :=
  e.init.all fun | [.refFunc _] => true | _ => false

/-- The `wast` crate encodes a `funcref` segment of function indices with `elemkind` `0x00`,
which the binary format reads as a `(ref func)` segment: the one place where its bytes and the
SpecTec text grammar assign different modules (`(table funcref (elem $f))` elaborates to a
`funcref` segment). `normElems` identifies the two types on such segments. -/
def normElem (e : Elem) : Elem :=
  if funcIndexItems e && e.type == funcrefT then { e with type := funcNonNullT } else e

def normElems (m : Wasm.Module) : Wasm.Module := { m with elems := m.elems.map normElem }

/-- The candidate decodes to a module equal to `m` up to `normElems` (both normal forms have
the same certified encoding). -/
def acceptsNorm (dc : Bool) (m : Wasm.Module) (cand : List UInt8) : Bool :=
  match Binary.Core.Decode.decodeModule ⟨cand.toArray⟩ with
  | .ok m' =>
    match Binaryen.Exe.encodeModuleWith? dc (normElems m'),
        Binaryen.Exe.encodeModuleWith? dc (normElems m) with
    | .ok a, .ok b => a == b
    | _, _ => false
  | .error _ => false

/-- The checked encoding of a core module text (see the module docstring). -/
def checkedCore (src : String) (cand : Except String ByteArray) : Except String ByteArray :=
  match Text.textTree? src with
  | .ok (_, m) =>
    let dc := Binaryen.Exe.usesDataIdx m
    match Binaryen.Exe.encodeModuleWith? dc m, cand with
    | .ok canon, .ok c =>
      if Layout.accepts dc canon c.data.toList then .ok c
      else if acceptsNorm dc m c.data.toList then .ok c
      else Text.textToBinary src
    | .ok _, .error _ => Text.textToBinary src
    | .error _, _ => cand
  | .error _ => cand

end Silmaril.Wasm.Tools.Wast
