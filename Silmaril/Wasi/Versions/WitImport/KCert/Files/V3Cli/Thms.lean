module

public import Silmaril.Wasi.Versions.WitImport.KQuote.Defs

@[expose] public section

/-!
# Kernel parse certificates: `0.3.2/cli`

For each file `f`: `KF.….src` is `wit_srcnd% "f"` (the glued text without doc comments,
`Silmaril.Wasi.Versions.WitImport.KSrcNd`), `KF.….d` the document it parses to, and `KF.….parse :
parseCharsK KF.….src = some (KF.….d String.ofList)`, checked by the kernel (`kernel_rfl`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfile KF.v3.cli.environment "../../../../../../../specs/wasi/0.3.2/cli/environment.wit"
wit_kfile KF.v3.cli.exit "../../../../../../../specs/wasi/0.3.2/cli/exit.wit"
wit_kfile KF.v3.cli.run "../../../../../../../specs/wasi/0.3.2/cli/run.wit"
wit_kfile KF.v3.cli.stdio "../../../../../../../specs/wasi/0.3.2/cli/stdio.wit"
wit_kfile KF.v3.cli.terminal "../../../../../../../specs/wasi/0.3.2/cli/terminal.wit"

end Silmaril.Wasi.Versions.WitImport
