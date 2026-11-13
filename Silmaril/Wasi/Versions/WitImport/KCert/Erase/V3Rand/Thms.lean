module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Rand.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Defs

@[expose] public section

/-!
# Doc comments only fill `docs` fields: `V3Rand`

For each file, `KF.….parseEr`: the verified parser on the glued text with its doc comments
(`KF.….full`, `wit_src%`), with every `docs` field then erased (`Document.erase`), gives the
document of the text without doc comments (`KF.….src`, `wit_srcnd%`). Checked by the kernel
(`kernel_rfl`); the kernel never evaluates the doc strings, which the erasure discards.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `specs/wasi/0.3.2/random/insecure-seed.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.rand.insecure_seed.parseEr :
    (parseCharsK KF.v3.rand.insecure_seed.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.rand.insecure_seed.src :=
  (show (parseCharsK KF.v3.rand.insecure_seed.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.rand.insecure_seed.d String.ofList) by
    kernel_rfl).trans KF.v3.rand.insecure_seed.parse.symm

/-- `specs/wasi/0.3.2/random/insecure.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.rand.insecure.parseEr :
    (parseCharsK KF.v3.rand.insecure.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.rand.insecure.src :=
  (show (parseCharsK KF.v3.rand.insecure.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.rand.insecure.d String.ofList) by
    kernel_rfl).trans KF.v3.rand.insecure.parse.symm

/-- `specs/wasi/0.3.2/random/random.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.rand.random.parseEr :
    (parseCharsK KF.v3.rand.random.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.rand.random.src :=
  (show (parseCharsK KF.v3.rand.random.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.rand.random.d String.ofList) by
    kernel_rfl).trans KF.v3.rand.random.parse.symm

end Silmaril.Wasi.Versions.WitImport
