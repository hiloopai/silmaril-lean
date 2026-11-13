module

public import Silmaril.Wasm.Tools.Component.Wat.Defs
public import Silmaril.Proofs.Wasm.Tools.Component.Wat.RoundTrip

/-!
# Component WAT with every built-in: verified printing and reading

Proofs in `Silmaril.Proofs.Wasm.Tools.Component.Wat.{Canon,RoundTrip}`:

* `item_canon : R.item (P.canon c) = some (.canons [c])`: every built-in of `Binary.md` at
  `d095e2f` reads back (`bkOf?_name`: each keyword names its built-in);
* `read_print : read (print c) = some (norm c)`, `ofSexp_toSexp`, `wf_toSexp`: the round
  trip modulo `Wat`'s normal form, reusing `Silmaril.Wasm.Component.Wat`'s lemmas for every
  other item (`Bridge`, `section_rt_v0`);
* `readX_print`: the tool's reader (`readX`, with `Wac.WatX`'s expansion as fallback) reads the
  printer's text with the verified reader;
* `parseText_printBytes`: `wasm-tools parse` of what `wasm-tools print` wrote for a binary `b`
  is the encoding of the normal form of `b`'s decoding; `parse_print_decode`: on a normal
  form, the bytes decode back to the same component (`BinaryP3.parse_encode`).

Not proved: anything about text the printer did not write (the `Wac.WatX` expansion of
identifiers, abbreviations and text core modules is unverified tooling), and the layout of
`wasm-tools print` (this printer's layout is `Sexp.printAll`'s).
-/
