module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Fs.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Quote.Defs

@[expose] public section

/-!
# The tokens of `specs/wasi/0.3.2/filesystem/types.wit` with its doc comments

`KF.v3.fs.types.toksF` and `KF.v3.fs.types.lexF : lexK (KF.v3.fs.types.full.length + 1) KF.v3.fs.types.full = some (KF.v3.fs.types.toksF String.ofList)`
(`wit_kfulltoks`, `Silmaril.Wasi.Versions.WitImport.KErase.Quote`), checked by the kernel. The parser
run on these tokens is checked in `KCert/Erase/V3Fs`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfulltoks KF.v3.fs.types "../../../../../../../specs/wasi/0.3.2/filesystem/types.wit"

end Silmaril.Wasi.Versions.WitImport
