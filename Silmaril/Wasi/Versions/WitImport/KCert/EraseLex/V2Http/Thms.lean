module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Http.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Quote.Defs

@[expose] public section

/-!
# The tokens of `specs/wasi/0.2.12/http/types.wit` with its doc comments

`KF.v2.http.types.toksF` and `KF.v2.http.types.lexF : lexK (KF.v2.http.types.full.length + 1) KF.v2.http.types.full = some (KF.v2.http.types.toksF String.ofList)`
(`wit_kfulltoks`, `Silmaril.Wasi.Versions.WitImport.KErase.Quote`), checked by the kernel. The parser
run on these tokens is checked in `KCert/Erase/V2Http`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfulltoks KF.v2.http.types "../../../../../../../specs/wasi/0.2.12/http/types.wit"

end Silmaril.Wasi.Versions.WitImport
