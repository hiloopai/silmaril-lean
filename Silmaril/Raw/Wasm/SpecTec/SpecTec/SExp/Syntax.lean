module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.ParseVerified
public import Silmaril.Semantics.CPort.Formats.SExp.Syntax.Defs

/-!
# SpecTec's `--ast` dialect as a `TreeSyntax`

The verified stream reader `parseStream?` and the width-`w` printer
`astFile w` form a syntax per width. Its round-trip law is
`parseStream?_astFile` on the printable fragment. The dialect is not
canonical: any layout is accepted (`not_streamRel_deterministic`).
-/

@[expose] public section

namespace Silmaril.SpecTec.SExp

open Silmaril.Formats

/-- SpecTec's AST stream syntax at a given layout width. -/
def astFileSyntax (width : Nat) : TreeSyntax String (List SExp) where
  print := astFile width
  parse := parseStream?

theorem astFileSyntax_roundTripOn (width : Nat) :
    (astFileSyntax width).RoundTripOn PrintableList :=
  fun es h => parseStream?_astFile width es h

/-- The syntax's relation is the lexical stream convention. -/
theorem astFileSyntax_rel (width : Nat) : (astFileSyntax width).rel = streamRel :=
  streamRel_eq_ofDecoder.symm

end Silmaril.SpecTec.SExp
