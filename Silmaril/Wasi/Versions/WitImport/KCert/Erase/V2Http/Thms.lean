module

public import Silmaril.Wasi.Versions.WitImport.KCert.EraseLex.V2Http.Thms

@[expose] public section

/-!
# Doc comments only fill `docs` fields: `V2Http`

`KF.v2.http.types.parseEr`: the verified parser on the glued text of `specs/wasi/0.2.12/http/types.wit` with its doc comments
(`KF.v2.http.types.full`, `wit_src%`), with every `docs` field then erased (`Document.erase`), gives the
document of the text without doc comments (`KF.v2.http.types.src`, `wit_srcnd%`). The lexer run is checked in
`KCert/EraseLex/V2Http` (`KF.v2.http.types.lexF`); here the kernel checks the parser run on the quoted tokens
(`kernel_rfl`), without evaluating the doc strings, which the erasure discards.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- The parser on the quoted tokens with doc comments, erased. -/
theorem KF.v2.http.types.parseTokEr :
    (Silmaril.Wasm.Wit.Text.Parse.document (KF.v2.http.types.toksF String.ofList)).map Silmaril.Wasm.Wit.Document.erase =
      some (KF.v2.http.types.d String.ofList) := by
  kernel_rfl

/-- `specs/wasi/0.2.12/http/types.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v2.http.types.parseEr :
    (parseCharsK KF.v2.http.types.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v2.http.types.src := by
  have hl : parseCharsK KF.v2.http.types.full = Silmaril.Wasm.Wit.Text.Parse.document (KF.v2.http.types.toksF String.ofList) := by
    unfold parseCharsK
    rw [KF.v2.http.types.lexF]
    rfl
  rw [hl, KF.v2.http.types.parseTokEr, KF.v2.http.types.parse]

end Silmaril.Wasi.Versions.WitImport
