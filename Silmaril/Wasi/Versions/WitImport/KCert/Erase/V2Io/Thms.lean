module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Io.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Defs

@[expose] public section

/-!
# Doc comments only fill `docs` fields: `V2Io`

For each file, `KF.….parseEr`: the verified parser on the glued text with its doc comments
(`KF.….full`, `wit_src%`), with every `docs` field then erased (`Document.erase`), gives the
document of the text without doc comments (`KF.….src`, `wit_srcnd%`). Checked by the kernel
(`kernel_rfl`); the kernel never evaluates the doc strings, which the erasure discards.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `specs/wasi/0.2.12/io/error.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v2.io.error.parseEr :
    (parseCharsK KF.v2.io.error.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v2.io.error.src :=
  (show (parseCharsK KF.v2.io.error.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v2.io.error.d String.ofList) by
    kernel_rfl).trans KF.v2.io.error.parse.symm

/-- `specs/wasi/0.2.12/io/poll.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v2.io.poll.parseEr :
    (parseCharsK KF.v2.io.poll.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v2.io.poll.src :=
  (show (parseCharsK KF.v2.io.poll.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v2.io.poll.d String.ofList) by
    kernel_rfl).trans KF.v2.io.poll.parse.symm

/-- `specs/wasi/0.2.12/io/streams.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v2.io.streams.parseEr :
    (parseCharsK KF.v2.io.streams.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v2.io.streams.src :=
  (show (parseCharsK KF.v2.io.streams.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v2.io.streams.d String.ofList) by
    kernel_rfl).trans KF.v2.io.streams.parse.symm

end Silmaril.Wasi.Versions.WitImport
