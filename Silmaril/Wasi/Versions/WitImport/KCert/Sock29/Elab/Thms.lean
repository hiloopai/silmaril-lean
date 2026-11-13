module

public import Silmaril.Wasi.Versions.WitImport.KCert.Sock29.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:sockets@0.2.9`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.sock29.envEq`, the worlds, `KC.sock29.pkg`,
`KC.sock29.valid`, `KC.sock29.unique`, `KC.sock29.elab` and `KC.sock29.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.sock29 env from unversioned all [KF.v29.sock.network, KF.v29.sock.instance_network, KF.v29.sock.tcp, KF.v29.sock.tcp_create_socket, KF.v29.sock.udp, KF.v29.sock.udp_create_socket, KF.v29.sock.ip_name_lookup, KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/sockets/network.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/instance-network.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/tcp.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/tcp-create-socket.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/udp.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/udp-create-socket.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/ip-name-lookup.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.sock29 world from unversioned all [KF.v29.sock.network, KF.v29.sock.instance_network, KF.v29.sock.tcp, KF.v29.sock.tcp_create_socket, KF.v29.sock.udp, KF.v29.sock.udp_create_socket, KF.v29.sock.ip_name_lookup, KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/sockets/network.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/instance-network.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/tcp.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/tcp-create-socket.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/udp.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/udp-create-socket.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/ip-name-lookup.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.sock29 final from unversioned all [KF.v29.sock.network, KF.v29.sock.instance_network, KF.v29.sock.tcp, KF.v29.sock.tcp_create_socket, KF.v29.sock.udp, KF.v29.sock.udp_create_socket, KF.v29.sock.ip_name_lookup, KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/sockets/network.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/instance-network.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/tcp.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/tcp-create-socket.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/udp.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/udp-create-socket.wit"
  "../../../../../../../specs/wasi/v0.2.9/sockets/ip-name-lookup.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport
