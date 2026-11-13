module

public import Silmaril.Wasi.Versions.WitImport.KQuote.Defs

@[expose] public section

/-!
# Kernel parse certificates: `0.2.12/random`

For each file `f`: `KF.….src` is `wit_srcnd% "f"` (the glued text without doc comments,
`Silmaril.Wasi.Versions.WitImport.KSrcNd`), `KF.….d` the document it parses to, and `KF.….parse :
parseCharsK KF.….src = some (KF.….d String.ofList)`, checked by the kernel (`kernel_rfl`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfile KF.v2.rand.insecure_seed "../../../../../../../specs/wasi/0.2.12/random/insecure-seed.wit"
wit_kfile KF.v2.rand.insecure "../../../../../../../specs/wasi/0.2.12/random/insecure.wit"
wit_kfile KF.v2.rand.random "../../../../../../../specs/wasi/0.2.12/random/random.wit"

end Silmaril.Wasi.Versions.WitImport
