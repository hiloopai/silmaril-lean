module

public import Silmaril.Wasi.Versions.WitImport.KCert.EraseLex.V3Http2.Thms

@[expose] public section

/-!
# Doc comments only fill `docs` fields: `V3Http2`

`KF.v3.http.types.parseEr`: the verified parser on the glued text of `specs/wasi/0.3.2/http/types.wit` with its doc comments
(`KF.v3.http.types.full`, `wit_src%`), with every `docs` field then erased (`Document.erase`), gives the
document of the text without doc comments (`KF.v3.http.types.src`, `wit_srcnd%`). The lexer run is checked in
`KCert/EraseLex/V3Http2` (`KF.v3.http.types.lexF`); here the kernel checks the parser run on the quoted tokens
(`kernel_rfl`), without evaluating the doc strings, which the erasure discards.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- The parser on the quoted tokens with doc comments, erased. -/
theorem KF.v3.http.types.parseTokEr :
    (Silmaril.Wasm.Wit.Text.Parse.document (KF.v3.http.types.toksF String.ofList)).map Silmaril.Wasm.Wit.Document.erase =
      some (KF.v3.http.types.d String.ofList) := by
  kernel_rfl

/-- `specs/wasi/0.3.2/http/types.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.http.types.parseEr :
    (parseCharsK KF.v3.http.types.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.http.types.src := by
  have hl : parseCharsK KF.v3.http.types.full = Silmaril.Wasm.Wit.Text.Parse.document (KF.v3.http.types.toksF String.ofList) := by
    unfold parseCharsK
    rw [KF.v3.http.types.lexF]
    rfl
  rw [hl, KF.v3.http.types.parseTokEr, KF.v3.http.types.parse]

end Silmaril.Wasi.Versions.WitImport
