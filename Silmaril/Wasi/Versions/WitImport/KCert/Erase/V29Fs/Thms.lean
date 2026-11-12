module

public import Silmaril.Wasi.Versions.WitImport.KCert.EraseLex.V29Fs.Thms

@[expose] public section

/-!
# Doc comments only fill `docs` fields: `V29Fs`

`KF.v29.fs.types.parseEr`: the verified parser on the glued text of `specs/wasi/v0.2.9/filesystem/types.wit` with its doc comments
(`KF.v29.fs.types.full`, `wit_src%`), with every `docs` field then erased (`Document.erase`), gives the
document of the text without doc comments (`KF.v29.fs.types.src`, `wit_srcnd%`). The lexer run is checked in
`KCert/EraseLex/V29Fs` (`KF.v29.fs.types.lexF`); here the kernel checks the parser run on the quoted tokens
(`kernel_rfl`), without evaluating the doc strings, which the erasure discards.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- The parser on the quoted tokens with doc comments, erased. -/
theorem KF.v29.fs.types.parseTokEr :
    (Silmaril.Wasm.Wit.Text.Parse.document (KF.v29.fs.types.toksF String.ofList)).map Silmaril.Wasm.Wit.Document.erase =
      some (KF.v29.fs.types.d String.ofList) := by
  kernel_rfl

/-- `specs/wasi/v0.2.9/filesystem/types.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v29.fs.types.parseEr :
    (parseCharsK KF.v29.fs.types.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v29.fs.types.src := by
  have hl : parseCharsK KF.v29.fs.types.full = Silmaril.Wasm.Wit.Text.Parse.document (KF.v29.fs.types.toksF String.ofList) := by
    unfold parseCharsK
    rw [KF.v29.fs.types.lexF]
    rfl
  rw [hl, KF.v29.fs.types.parseTokEr, KF.v29.fs.types.parse]

end Silmaril.Wasi.Versions.WitImport
