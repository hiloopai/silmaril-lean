module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Sock.Thms
public import Silmaril.Wasi.Versions.WitImport.KNoDoc.Thms

@[expose] public section

/-!
# Doc comments only remove tokens: `0.2.12/sockets`

For each file (`wit_klex`, `Silmaril.Wasi.Versions.WitImport.KQuote`), `KF.….lexNd`: the tokens of the
demoted text `KF.….src` (`wit_srcnd%`) are the tokens of the text with its docs `KF.….full`
(`wit_src%`) without the doc-comment tokens, checked by the kernel through the quoted tokens
`KF.….toks` (`kernel_rfl`); `KF.….parseNd : parseCharsK KF.….src = parseTokK KF.….full`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_klex KF.v2.sock.network "../../../../../../../specs/wasi/0.2.12/sockets/network.wit"
wit_klex KF.v2.sock.instance_network "../../../../../../../specs/wasi/0.2.12/sockets/instance-network.wit"

end Silmaril.Wasi.Versions.WitImport
