module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Http.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Quote.Defs

@[expose] public section

/-!
# The tokens of `specs/wasi/v0.2.9/http/types.wit` with its doc comments

`KF.v29.http.types.toksF` and `KF.v29.http.types.lexF : lexK (KF.v29.http.types.full.length + 1) KF.v29.http.types.full = some (KF.v29.http.types.toksF String.ofList)`
(`wit_kfulltoks`, `Silmaril.Wasi.Versions.WitImport.KErase.Quote`), checked by the kernel. The parser
run on these tokens is checked in `KCert/Erase/V29Http`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfulltoks KF.v29.http.types "../../../../../../../specs/wasi/v0.2.9/http/types.wit"

end Silmaril.Wasi.Versions.WitImport
