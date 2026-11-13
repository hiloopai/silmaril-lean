module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V29Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V29Io.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V29Sock.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:sockets@0.2.9`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.sock29.U` and `KC.sock29.univ`, its validity `KC.sock29.check`, and one `Elab.elabBody`
equation per interface (`KC.sock29.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.sock29 univ from unversioned all [KF.v29.sock.network, KF.v29.sock.instance_network, KF.v29.sock.tcp, KF.v29.sock.tcp_create_socket, KF.v29.sock.udp, KF.v29.sock.udp_create_socket, KF.v29.sock.ip_name_lookup, KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
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

wit_kcert KC.sock29 check from unversioned all [KF.v29.sock.network, KF.v29.sock.instance_network, KF.v29.sock.tcp, KF.v29.sock.tcp_create_socket, KF.v29.sock.udp, KF.v29.sock.udp_create_socket, KF.v29.sock.ip_name_lookup, KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
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

wit_kcert KC.sock29 body from unversioned all [KF.v29.sock.network, KF.v29.sock.instance_network, KF.v29.sock.tcp, KF.v29.sock.tcp_create_socket, KF.v29.sock.udp, KF.v29.sock.udp_create_socket, KF.v29.sock.ip_name_lookup, KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
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
