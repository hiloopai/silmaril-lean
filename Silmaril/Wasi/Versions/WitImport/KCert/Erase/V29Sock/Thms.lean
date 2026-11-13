module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Sock.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Defs

@[expose] public section

/-!
# Doc comments only fill `docs` fields: `V29Sock`

For each file, `KF.….parseEr`: the verified parser on the glued text with its doc comments
(`KF.….full`, `wit_src%`), with every `docs` field then erased (`Document.erase`), gives the
document of the text without doc comments (`KF.….src`, `wit_srcnd%`). Checked by the kernel
(`kernel_rfl`); the kernel never evaluates the doc strings, which the erasure discards.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `specs/wasi/v0.2.9/sockets/network.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v29.sock.network.parseEr :
    (parseCharsK KF.v29.sock.network.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v29.sock.network.src :=
  (show (parseCharsK KF.v29.sock.network.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v29.sock.network.d String.ofList) by
    kernel_rfl).trans KF.v29.sock.network.parse.symm

/-- `specs/wasi/v0.2.9/sockets/instance-network.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v29.sock.instance_network.parseEr :
    (parseCharsK KF.v29.sock.instance_network.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v29.sock.instance_network.src :=
  (show (parseCharsK KF.v29.sock.instance_network.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v29.sock.instance_network.d String.ofList) by
    kernel_rfl).trans KF.v29.sock.instance_network.parse.symm

end Silmaril.Wasi.Versions.WitImport
