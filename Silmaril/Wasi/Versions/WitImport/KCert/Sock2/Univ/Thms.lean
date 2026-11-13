module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Io.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Sock.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:sockets@0.2.12`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.sock2.U` and `KC.sock2.univ`, its validity `KC.sock2.check`, and one `Elab.elabBody`
equation per interface (`KC.sock2.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.sock2 univ from unversioned all [KF.v2.sock.network, KF.v2.sock.instance_network, KF.v2.sock.tcp, KF.v2.sock.tcp_create_socket, KF.v2.sock.udp, KF.v2.sock.udp_create_socket, KF.v2.sock.ip_name_lookup, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/sockets/network.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/instance-network.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/tcp.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/tcp-create-socket.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/udp.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/udp-create-socket.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/ip-name-lookup.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.sock2 check from unversioned all [KF.v2.sock.network, KF.v2.sock.instance_network, KF.v2.sock.tcp, KF.v2.sock.tcp_create_socket, KF.v2.sock.udp, KF.v2.sock.udp_create_socket, KF.v2.sock.ip_name_lookup, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/sockets/network.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/instance-network.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/tcp.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/tcp-create-socket.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/udp.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/udp-create-socket.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/ip-name-lookup.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.sock2 body from unversioned all [KF.v2.sock.network, KF.v2.sock.instance_network, KF.v2.sock.tcp, KF.v2.sock.tcp_create_socket, KF.v2.sock.udp, KF.v2.sock.udp_create_socket, KF.v2.sock.ip_name_lookup, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/sockets/network.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/instance-network.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/tcp.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/tcp-create-socket.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/udp.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/udp-create-socket.wit"
  "../../../../../../../specs/wasi/0.2.12/sockets/ip-name-lookup.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport
