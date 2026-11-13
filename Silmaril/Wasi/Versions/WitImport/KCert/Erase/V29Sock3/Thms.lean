module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Sock3.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Defs

@[expose] public section

/-!
# Doc comments only fill `docs` fields: `V29Sock3`

For each file, `KF.….parseEr`: the verified parser on the glued text with its doc comments
(`KF.….full`, `wit_src%`), with every `docs` field then erased (`Document.erase`), gives the
document of the text without doc comments (`KF.….src`, `wit_srcnd%`). Checked by the kernel
(`kernel_rfl`); the kernel never evaluates the doc strings, which the erasure discards.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `specs/wasi/v0.2.9/sockets/udp.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v29.sock.udp.parseEr :
    (parseCharsK KF.v29.sock.udp.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v29.sock.udp.src :=
  (show (parseCharsK KF.v29.sock.udp.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v29.sock.udp.d String.ofList) by
    kernel_rfl).trans KF.v29.sock.udp.parse.symm

/-- `specs/wasi/v0.2.9/sockets/udp-create-socket.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v29.sock.udp_create_socket.parseEr :
    (parseCharsK KF.v29.sock.udp_create_socket.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v29.sock.udp_create_socket.src :=
  (show (parseCharsK KF.v29.sock.udp_create_socket.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v29.sock.udp_create_socket.d String.ofList) by
    kernel_rfl).trans KF.v29.sock.udp_create_socket.parse.symm

/-- `specs/wasi/v0.2.9/sockets/ip-name-lookup.wit`: its parse with doc comments, erased, is the parse without them. -/
theorem KF.v29.sock.ip_name_lookup.parseEr :
    (parseCharsK KF.v29.sock.ip_name_lookup.full).map Silmaril.Wasm.Wit.Document.erase = parseCharsK KF.v29.sock.ip_name_lookup.src :=
  (show (parseCharsK KF.v29.sock.ip_name_lookup.full).map Silmaril.Wasm.Wit.Document.erase = some (KF.v29.sock.ip_name_lookup.d String.ofList) by
    kernel_rfl).trans KF.v29.sock.ip_name_lookup.parse.symm

end Silmaril.Wasi.Versions.WitImport
