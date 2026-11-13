module

public import Silmaril.Wasi.Versions.WitImport.KQuote.Defs

@[expose] public section

/-!
# Kernel parse certificates: `0.2.12/filesystem`

For each file `f`: `KF.….src` is `wit_srcnd% "f"` (the glued text without doc comments,
`Silmaril.Wasi.Versions.WitImport.KSrcNd`), `KF.….d` the document it parses to, and `KF.….parse :
parseCharsK KF.….src = some (KF.….d String.ofList)`, checked by the kernel (`kernel_rfl`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfile KF.v2.fs.types "../../../../../../../specs/wasi/0.2.12/filesystem/types.wit"
wit_kfile KF.v2.fs.preopens "../../../../../../../specs/wasi/0.2.12/filesystem/preopens.wit"

end Silmaril.Wasi.Versions.WitImport
