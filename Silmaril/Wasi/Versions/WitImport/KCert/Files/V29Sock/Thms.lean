module

public import Silmaril.Wasi.Versions.WitImport.KQuote.Defs

@[expose] public section

/-!
# Kernel parse certificates: `v0.2.9/sockets`

For each file `f`: `KF.….src` is `wit_srcnd% "f"` (the glued text without doc comments,
`Silmaril.Wasi.Versions.WitImport.KSrcNd`), `KF.….d` the document it parses to, and `KF.….parse :
parseCharsK KF.….src = some (KF.….d String.ofList)`, checked by the kernel (`kernel_rfl`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfile KF.v29.sock.network "../../../../../../../specs/wasi/v0.2.9/sockets/network.wit"
wit_kfile KF.v29.sock.instance_network "../../../../../../../specs/wasi/v0.2.9/sockets/instance-network.wit"
wit_kfile KF.v29.sock.tcp "../../../../../../../specs/wasi/v0.2.9/sockets/tcp.wit"
wit_kfile KF.v29.sock.tcp_create_socket "../../../../../../../specs/wasi/v0.2.9/sockets/tcp-create-socket.wit"
wit_kfile KF.v29.sock.udp "../../../../../../../specs/wasi/v0.2.9/sockets/udp.wit"
wit_kfile KF.v29.sock.udp_create_socket "../../../../../../../specs/wasi/v0.2.9/sockets/udp-create-socket.wit"
wit_kfile KF.v29.sock.ip_name_lookup "../../../../../../../specs/wasi/v0.2.9/sockets/ip-name-lookup.wit"

end Silmaril.Wasi.Versions.WitImport
