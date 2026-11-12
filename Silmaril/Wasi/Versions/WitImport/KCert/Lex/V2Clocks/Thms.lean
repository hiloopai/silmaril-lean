module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KNoDoc.Thms

@[expose] public section

/-!
# Doc comments only remove tokens: `0.2.12/clocks`

For each file (`wit_klex`, `Silmaril.Wasi.Versions.WitImport.KQuote`), `KF.….lexNd`: the tokens of the
demoted text `KF.….src` (`wit_srcnd%`) are the tokens of the text with its docs `KF.….full`
(`wit_src%`) without the doc-comment tokens, checked by the kernel through the quoted tokens
`KF.….toks` (`kernel_rfl`); `KF.….parseNd : parseCharsK KF.….src = parseTokK KF.….full`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_klex KF.v2.clocks.monotonic_clock "../../../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
wit_klex KF.v2.clocks.wall_clock "../../../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
wit_klex KF.v2.clocks.timezone "../../../../../../../specs/wasi/0.2.12/clocks/timezone.wit"

end Silmaril.Wasi.Versions.WitImport
