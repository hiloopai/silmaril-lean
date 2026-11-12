module

public import Silmaril.Wasi.Versions.WitImport.KQuote.Defs

@[expose] public section

/-!
# Kernel parse certificates: `0.2.12/sockets`

For each file `f`: `KF.….src` is `wit_srcnd% "f"` (the glued text without doc comments,
`Silmaril.Wasi.Versions.WitImport.KSrcNd`), `KF.….d` the document it parses to, and `KF.….parse :
parseCharsK KF.….src = some (KF.….d String.ofList)`, checked by the kernel (`kernel_rfl`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kfile KF.v2.sock.network "../../../../../../../specs/wasi/0.2.12/sockets/network.wit"
wit_kfile KF.v2.sock.instance_network "../../../../../../../specs/wasi/0.2.12/sockets/instance-network.wit"
wit_kfile KF.v2.sock.tcp "../../../../../../../specs/wasi/0.2.12/sockets/tcp.wit"
wit_kfile KF.v2.sock.tcp_create_socket "../../../../../../../specs/wasi/0.2.12/sockets/tcp-create-socket.wit"
wit_kfile KF.v2.sock.udp "../../../../../../../specs/wasi/0.2.12/sockets/udp.wit"
wit_kfile KF.v2.sock.udp_create_socket "../../../../../../../specs/wasi/0.2.12/sockets/udp-create-socket.wit"
wit_kfile KF.v2.sock.ip_name_lookup "../../../../../../../specs/wasi/0.2.12/sockets/ip-name-lookup.wit"

end Silmaril.Wasi.Versions.WitImport
