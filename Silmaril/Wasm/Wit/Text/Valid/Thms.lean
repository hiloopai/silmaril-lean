module

public import Silmaril.Raw.Wasm.Wit.Text.Valid

/-!
# WIT text: valid documents are printable

Proofs in `Silmaril.Raw.Wasm.Wit.Text.Valid` (and `Silmaril.Proofs.Wasm.Wit.Text.Chars`,
exported by `Silmaril.Wasm.Wit.Text.Thms`):

* `idOk_of_validId : ValidId s → idOk s = true`, `verOk_of_valid : v.Valid → verOk v = true`;
* `binds_validId`: a name bound in a scope of a valid universe is a valid identifier;
  `pathOk_of_resolves`: a resolved path is printable;
* `printable_of_valid : Valid (d.packages ++ deps) → printable d = true` and
  `printable_of_check`;
* `parse_print_of_valid : Valid (d.packages ++ deps) → parse (print d) = some (Document.norm d)`:
  the text round trip holds for every valid document.

This header is separate from `Silmaril.Wasm.Wit.Text.Thms` because it uses the
elaboration lemmas (`Silmaril.Wasm.Wit.Elab.Thms`), which themselves use the text
printer's version spelling.
-/
