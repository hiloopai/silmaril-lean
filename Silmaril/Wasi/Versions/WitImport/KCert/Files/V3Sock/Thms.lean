module

public import Silmaril.Wasi.Versions.WitImport.KQuote.Defs

@[expose] public section

/-!
# Kernel parse certificates: `0.3.2/sockets`

For each file `f`: `KF.….src` is `wit_srcnd% "f"` (the glued text without doc comments,
`Silmaril.Wasi.Versions.WitImport.KSrcNd`), `KF.….d` the document it parses to, and `KF.….parse :
parseCharsK KF.….src = some (KF.….d String.ofList)`, checked by the kernel (`kernel_rfl`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfile KF.v3.sock.types "../../../../../../../specs/wasi/0.3.2/sockets/types.wit"
wit_kfile KF.v3.sock.ip_name_lookup "../../../../../../../specs/wasi/0.3.2/sockets/ip-name-lookup.wit"

end Silmaril.Wasi.Versions.WitImport
