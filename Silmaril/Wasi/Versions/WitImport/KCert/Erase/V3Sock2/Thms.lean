module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Sock2.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Defs

@[expose] public section

/-!
# Doc comments only fill `docs` fields: `V3Sock2`

For each file, `KF.….parseEr`: the verified parser on the glued text with its doc comments
(`KF.….full`, `wit_src%`), with every `docs` field then erased (`Document.erase`), gives the
document of the text without doc comments (`KF.….src`, `wit_srcnd%`). Checked by the kernel
(`kernel_rfl`); the kernel never evaluates the doc strings, which the erasure discards.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `specs/wasi/0.3.2/sockets/ip-name-lookup.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v3.sock.ip_name_lookup.parseEr :
    (parseCharsK KF.v3.sock.ip_name_lookup.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v3.sock.ip_name_lookup.src :=
  (show (parseCharsK KF.v3.sock.ip_name_lookup.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v3.sock.ip_name_lookup.d String.ofList) by
    kernel_rfl).trans KF.v3.sock.ip_name_lookup.parse.symm

end Silmaril.Wasi.Versions.WitImport
