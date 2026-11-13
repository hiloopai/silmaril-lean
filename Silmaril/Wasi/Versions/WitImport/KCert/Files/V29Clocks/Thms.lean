module

public import Silmaril.Wasi.Versions.WitImport.KQuote.Defs

@[expose] public section

/-!
# Kernel parse certificates: `v0.2.9/clocks`

For each file `f`: `KF.….src` is `wit_srcnd% "f"` (the glued text without doc comments,
`Silmaril.Wasi.Versions.WitImport.KSrcNd`), `KF.….d` the document it parses to, and `KF.….parse :
parseCharsK KF.….src = some (KF.….d String.ofList)`, checked by the kernel (`kernel_rfl`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfile KF.v29.clocks.monotonic_clock "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
wit_kfile KF.v29.clocks.wall_clock "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
wit_kfile KF.v29.clocks.timezone "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"

end Silmaril.Wasi.Versions.WitImport
