module

public import Silmaril.Wasm.Wit.Text.Parse.Defs
public import Silmaril.Proofs.Wasm.Wit.Text.RoundTrip
public import Silmaril.Proofs.Wasm.Wit.Text.Chars

/-!
# WIT text: verified reading and printing

Proofs in `Silmaril.Proofs.Wasm.Wit.Text.*`:

* `parse_print : printable d = true → parse (print d) = some (Document.norm d)`: the
  round trip, modulo the normal form (`async` dropped on resource constructors; the
  text has no spelling for it);
* `parse_render`: the same for every layout of the printed tokens (any whitespace and
  line breaks between them);
* `norm_eq_of_print_eq`: the printed text determines the normal form;
* the pieces: `lex_render` (every layout of printable tokens lexes back),
  `lex_lineComment`, `lex_lineComment'`, `lex_blockComment` (comments that are not doc
  comments are skipped), `ty_prTy`, `docs_prDocs`, `gates_prGates`,
  `parseVer_verChars`, `document_prDocument` (the parser inverts the printer on
  tokens), `okL_prDocument` (the printer writes lexable tokens).

Every theorem is proved; no `sorry` or axiom beyond Lean's.
-/
