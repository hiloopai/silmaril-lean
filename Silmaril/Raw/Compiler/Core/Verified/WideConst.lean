module

public import Silmaril.Compiler.Core.Spec.Defs
public import Silmaril.Cerberus.Codec.File.Defs
public import Silmaril.Cerberus.Codec.Tags.Defs
/-! # Spec-trust restriction: wide and Unicode character constants

Cerberus decodes every character constant into the range of plain `char`, whatever its
prefix (`Decode.decode_character_constant`, `ocaml_frontend/decode.ml`, wraps to the signed
8-bit range; `translation.lem` ignores the prefix of `ConstantCharacter` and decodes each
element of a wide string literal the same way before `conv_int` to the element type). So
the Core document of `L'\xff'` holds `-1` where C (and gcc) has 255, and `L'\x1234'` holds
52 where C has 4660; `u"\xff"[0]` is 65535 in Core and 255 in C. The verified compiler
implements the Core document faithfully, so such a program compiles to a binary whose
output differs from gcc's. `SoundSpec` is not violated (it is about the Core program), but
the Core program is not the C program.

The constants that carry the bug keep their C type in the document: a wide character
constant is an expression annotated `Avalue (Ainteger Wchar_t)` (`L`) or
`Ainteger (Unsigned (Int_leastN_t 16 | 32))` (`u`, `U`, Cerberus's `char16_t` and
`char32_t`), and a wide string literal is a global array of those element types.
`mentioned doc` searches the program's own globals and procedures (not the Core standard
library, not the implementation constants, not the declarations of `funInfo`) for these
integer types; `restrict c` rejects every document where they occur. This is
over-approximate (it also rejects objects of these types, which no fragment compiles),
because a decoded value cannot tell `L'4'` from a truncated `L'\x1234'`.

Not covered (the Core document keeps no trace of it): an enumerator initialised by a wide
constant, `enum { A = L'\xff' }`, is folded by Cerberus to the `int` literal `-1`.
`u8` strings are ordinary `char` arrays in Core, with the bytes gcc emits. See
`docs/projects/cerberus.md` ("Spec-trust restrictions"); the restriction is lifted when the
exporter decodes wide constants in their own type.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.WideConst

open Silmaril.Cerberus Silmaril.TaggedCodec
open Spec

/-- The tree mentions `wchar_t` or an `int_leastN_t` type (`char16_t`, `char32_t`). -/
def wideTree (t : Tree) : Bool :=
  t.fold (fun _ => false) fun tag children =>
    tag == tag% IntegerType.wchar || tag == tag% IntegerBaseType.intLeastN || children.any id

/-- A global or procedure of the program mentions a wide character type. -/
def mentioned (doc : Codec.Document) : Bool :=
  doc.bindings.globs.any (fun g => wideTree (Codec.global.enc g.2)) ||
    doc.bindings.funs.any (fun f => wideTree (Codec.funDecl.enc f.2))

/-- `c` on the documents that mention no wide character type, `none` on the others. -/
def restrict (c : Codec.Document → Option Artifact) (doc : Codec.Document) : Option Artifact :=
  if mentioned doc then none else c doc

theorem restrict_sound {c : Codec.Document → Option Artifact} (h : SoundSpec c) :
    SoundSpec (restrict c) := by
  intro doc a hc
  unfold restrict at hc
  split at hc
  · cases hc
  · exact h doc a hc

end Silmaril.Compile.Core.Verified.WideConst
