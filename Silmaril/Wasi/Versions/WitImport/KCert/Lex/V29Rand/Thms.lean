module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V29Rand.Thms
public import Silmaril.Wasi.Versions.WitImport.KNoDoc.Thms

@[expose] public section

/-!
# Doc comments only remove tokens: `v0.2.9/random`

For each file (`wit_klex`, `Silmaril.Wasi.Versions.WitImport.KQuote`), `KF.….lexNd`: the tokens of the
demoted text `KF.….src` (`wit_srcnd%`) are the tokens of the text with its docs `KF.….full`
(`wit_src%`) without the doc-comment tokens, checked by the kernel through the quoted tokens
`KF.….toks` (`kernel_rfl`); `KF.….parseNd : parseCharsK KF.….src = parseTokK KF.….full`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_klex KF.v29.rand.insecure_seed "../../../../../../../specs/wasi/v0.2.9/random/insecure-seed.wit"
wit_klex KF.v29.rand.insecure "../../../../../../../specs/wasi/v0.2.9/random/insecure.wit"
wit_klex KF.v29.rand.random "../../../../../../../specs/wasi/v0.2.9/random/random.wit"

end Silmaril.Wasi.Versions.WitImport
