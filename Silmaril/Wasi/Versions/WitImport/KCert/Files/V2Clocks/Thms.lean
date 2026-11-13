module

public import Silmaril.Wasi.Versions.WitImport.KQuote.Defs

@[expose] public section

/-!
# Kernel parse certificates: `0.2.12/clocks`

For each file `f`: `KF.….src` is `wit_srcnd% "f"` (the glued text without doc comments,
`Silmaril.Wasi.Versions.WitImport.KSrcNd`), `KF.….d` the document it parses to, and `KF.….parse :
parseCharsK KF.….src = some (KF.….d String.ofList)`, checked by the kernel (`kernel_rfl`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfile KF.v2.clocks.monotonic_clock "../../../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
wit_kfile KF.v2.clocks.wall_clock "../../../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
wit_kfile KF.v2.clocks.timezone "../../../../../../../specs/wasi/0.2.12/clocks/timezone.wit"

end Silmaril.Wasi.Versions.WitImport
