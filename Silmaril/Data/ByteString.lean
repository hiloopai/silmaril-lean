module

public import Init.Data.BitVec

/-! # Byte-string literals and readable UTF-8 byte lists

`b"adler32" : List (BitVec 8)` expands to byte constructors during macro
expansion. The source must be ASCII; standard string escapes are supported and
`b"\x80"` contains the single byte `0x80`. No terminator is added.

The pure compatibility helper `Silmaril.ByteString.utf8 "adler32"` instead
encodes UTF-8, so `utf8 "\x80"` is `[0xc2, 0x80]`. Raw byte lists need not be
valid UTF-8. This module has Init-only imports; no Lean or Mathlib import is
needed to define or use the macro.
-/

@[expose] public section
namespace Silmaril.ByteString

/-- Encode the existing UTF-8 representation, without decoding, normalization
or a trailing zero byte. Raw byte lists need not be valid UTF-8. -/
def utf8 (text : String) : List (BitVec 8) :=
  text.toByteArray.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat

@[simp] theorem utf8_empty : utf8 "" = [] := by rfl

/-- Adjacent `b"..."` is a raw byte list, with ASCII source and eight-bit escapes.
The prefix is parsed as an ordinary identifier, so importing the notation does
not reserve `b` in binders. Other adjacent identifier/string applications retain
their usual meaning; the fallback quotation contains a separating space. -/
macro:max (priority := high) head:ident noWs literal:str : term => do
  if head.getId != `b then
    `($head $literal)
  else do
    let source ← match literal.raw with
      | .node _ _ #[.atom _ source] => pure source
      | .atom _ source => pure source
      | _ => Lean.Macro.throwErrorAt literal "unsupported byte string syntax"
    if source.toList.any (fun char => char.toNat > 127) then
      Lean.Macro.throwErrorAt literal "byte string source must be ASCII; use hexadecimal escapes"
    let mut elements : Array (Lean.TSyntax `term) := #[]
    for char in literal.getString.toList do
      if char.toNat > 255 then
        Lean.Macro.throwErrorAt literal "byte string escape is outside 0..255"
      elements := elements.push (Lean.Syntax.mkNumLit (toString char.toNat))
    `(([$[$elements],*] : List (BitVec 8)))

end Silmaril.ByteString
