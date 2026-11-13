module

public import Silmaril.Wasi.Versions.WitImport.KNoDoc.Defs

@[expose] public section

/-!
# Parsing without doc-comment tokens

`parseCharsK_of_lex`: when the tokens of `cs` are those of `full` without the doc-comment tokens
(`notDoc`), parsing `cs` is parsing the tokens of `full` with the doc-comment tokens removed.
With `cs` the demoted text (`wit_srcnd%`) and `full` the text with its docs (`wit_src%`), the
hypothesis is checked per file in the kernel (`KCert/Lex/*`), so the kernel importer on the
demoted texts is the importer on the vendored texts' tokens without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- Parsing a text whose tokens are another text's tokens without doc comments. -/
theorem parseCharsK_of_lex {cs full : List Char}
    (h : (lexK (full.length + 1) full).map (List.filter notDoc) = lexK (cs.length + 1) cs) :
    parseCharsK cs =
      (lexK (full.length + 1) full).bind fun ts => Silmaril.Wasm.Wit.Text.Parse.document (ts.filter notDoc) := by
  unfold parseCharsK
  rw [← h]
  cases lexK (full.length + 1) full <;> rfl

end Silmaril.Wasi.Versions.WitImport
