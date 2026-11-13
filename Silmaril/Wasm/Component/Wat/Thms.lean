module

public import Silmaril.Wasm.Component.Wat.Defs
public import Silmaril.Wasm.Component.Wat.Sexp.Thms
public import Silmaril.Proofs.Wasm.Component.Wat.RoundTrip

/-!
# Component WAT: verified reading and printing

Proofs in `Silmaril.Proofs.Wasm.Component.Wat.*`:

* `read_print : read (print c) = some (norm c)` (the round trip, modulo the
  normal form of `Silmaril.Wasm.Component.Wat`: grouped sections, `0x00` names);
* `print_norm : print (norm c) = print c`, `norm_norm : norm (norm c) = norm c`;
* `print_eq_iff : print c = print d ↔ norm c = norm d`: the text determines the
  normal form and nothing more;
* `read_print_of_norm`: on normal forms the reader inverts the printer exactly;
* the pieces: `ofSexp_toSexp` (abstract syntax ↔ S-expressions),
  `Sexp.read_printAll` (S-expressions ↔ text), `wf_toSexp` (every printed atom is
  a keyword or a number).

Every theorem is proved; no `sorry` or axiom beyond Lean's.
-/
