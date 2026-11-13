module

public import Silmaril.Wasi.Versions.WitImport.KCert.Sock2.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:sockets@0.2.12`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.sock2.envEq`, the worlds, `KC.sock2.pkg`,
`KC.sock2.valid`, `KC.sock2.unique`, `KC.sock2.elab` and `KC.sock2.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.sock2 env from unversioned all [KF.v2.sock.network, KF.v2.sock.instance_network, KF.v2.sock.tcp, KF.v2.sock.tcp_create_socket, KF.v2.sock.udp, KF.v2.sock.udp_create_socket, KF.v2.sock.ip_name_lookup, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
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

wit_kcert KC.sock2 world from unversioned all [KF.v2.sock.network, KF.v2.sock.instance_network, KF.v2.sock.tcp, KF.v2.sock.tcp_create_socket, KF.v2.sock.udp, KF.v2.sock.udp_create_socket, KF.v2.sock.ip_name_lookup, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
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

wit_kcert KC.sock2 final from unversioned all [KF.v2.sock.network, KF.v2.sock.instance_network, KF.v2.sock.tcp, KF.v2.sock.tcp_create_socket, KF.v2.sock.udp, KF.v2.sock.udp_create_socket, KF.v2.sock.ip_name_lookup, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
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
