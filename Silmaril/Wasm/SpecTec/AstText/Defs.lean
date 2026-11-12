module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Encoding
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Printable
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.ParseVerified

/-!
# SpecTec `--ast` text to IL scripts

The reading of an `--ast` file, as one relation and one total function, composed from the
copied layers in `Silmaril.Raw.Wasm.SpecTec`:

* `AstTextRel s sc`: the text `s` lexes (`streamRel`, the lexical convention of
  `SExp/Lexical.lean`) to a list of S-expressions which is the printed form of the script `sc`
  (`IL.scriptRel`, the graph of `IL.scriptS`, transcribed from SpecTec's `print.ml`);
* `importAstText? s`: the verified reader `SExp.parseStream?` followed by the decoder
  `IL.decodeScript?`;
* `AstBytesRel`: the same, starting from UTF-8 bytes.

`spectec_import` (the elaboration-time import in `Import.lean`) does *not* use this reader; it
uses the unverified `SExp.parseStream`. `Silmaril.Proofs.Wasm.SpecTec.AstText.Streams` runs the
verified reader over the three pinned files at build time.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.AstText

open Silmaril (EncRel)
open Silmaril.SpecTec
open Silmaril.SpecTec.SExp (parseStream?)

/-- A text spells a script: it lexes to the script's printed S-expressions. -/
def AstTextRel : EncRel String IL.Script := fun s sc => ∃ es, streamRel s es ∧ IL.scriptRel es sc

/-- The verified `--ast` reader: lex with `parseStream?`, then decode with `decodeScript?`. -/
def importAstText? (s : String) : Option IL.Script := parseStream? s >>= IL.decodeScript?

/-- UTF-8 bytes spell a script when they decode to a text that does. -/
def AstBytesRel : EncRel ByteArray IL.Script :=
  fun b sc => ∃ s, String.fromUTF8? b = some s ∧ AstTextRel s sc

/-- The verified reader on bytes. -/
def importAstBytes? (b : ByteArray) : Option IL.Script := String.fromUTF8? b >>= importAstText?

end Silmaril.Wasm.SpecTec.AstText
