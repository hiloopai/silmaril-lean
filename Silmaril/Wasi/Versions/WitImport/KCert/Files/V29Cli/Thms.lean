module

public import Silmaril.Wasi.Versions.WitImport.KQuote.Defs

@[expose] public section

/-!
# Kernel parse certificates: `v0.2.9/cli`

For each file `f`: `KF.….src` is `wit_srcnd% "f"` (the glued text without doc comments,
`Silmaril.Wasi.Versions.WitImport.KSrcNd`), `KF.….d` the document it parses to, and `KF.….parse :
parseCharsK KF.….src = some (KF.….d String.ofList)`, checked by the kernel (`kernel_rfl`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfile KF.v29.cli.environment "../../../../../../../specs/wasi/v0.2.9/cli/environment.wit"
wit_kfile KF.v29.cli.exit "../../../../../../../specs/wasi/v0.2.9/cli/exit.wit"
wit_kfile KF.v29.cli.run "../../../../../../../specs/wasi/v0.2.9/cli/run.wit"
wit_kfile KF.v29.cli.stdio "../../../../../../../specs/wasi/v0.2.9/cli/stdio.wit"
wit_kfile KF.v29.cli.terminal "../../../../../../../specs/wasi/v0.2.9/cli/terminal.wit"

end Silmaril.Wasi.Versions.WitImport
