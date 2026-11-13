module

public import Silmaril.Wasm.Tools.Component.FastRead.Defs
public import Silmaril.Proofs.Wasm.Tools.Component.FastRead.Eq

/-!
# The tail-recursive reader: verified

Proofs in `Silmaril.Proofs.Wasm.Tools.Component.FastRead.Eq`:

* `lexStrA_eq`, `lexA_eq : lexA acc cs = (lex cs).map (acc.reverse ++ ·)`: the accumulating
  lexers are the lexers;
* `parseStk_sound`: the stack parser's result has exactly the tokens it read;
* `readF_eq : readF = Sexp.read`, `readXF_eq : readXF = Wat.readX` (`readXF` reads the
  text once, `Wat.readX` twice when the printer's spelling does not apply);
* `secF_eq`, `encodeF_eq : encodeF = BinaryP3.encode`: the encoder that appends sections to a
  `ByteArray` (core module and custom sections straight from their bytes) is the encoder;
* `parseTextF_eq : parseTextF = Wat.parseText`: the fast `wasm-tools parse` is the specified
  one, so `Wat.parse_print_decode` and `Layout.read_printW` apply to it.
-/
