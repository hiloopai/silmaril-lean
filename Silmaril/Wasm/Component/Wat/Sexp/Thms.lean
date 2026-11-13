module

public import Silmaril.Wasm.Component.Wat.Sexp.Defs
public import Silmaril.Proofs.Wasm.Component.Wat.Sexp

/-!
# S-expressions of WAT: verified reading

Proofs in `Silmaril.Proofs.Wasm.Component.Wat.Sexp`:

* `Sexp.read_print : WF s → read (print s) = some [s]`;
* `Sexp.read_printAll : WFL ss → read (printAll ss) = some ss`;
* the pieces: `lex_pp` (the lexer turns the printed characters into `toks s`,
  whatever the layout), `parseSeq_toksL` (the tree parser inverts `toks`).
-/
