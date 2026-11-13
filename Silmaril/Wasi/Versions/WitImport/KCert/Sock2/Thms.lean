module

public import Silmaril.Wasi.Versions.WitImport.KCert.Sock2.Elab.Thms
public import Silmaril.Wasi.Versions.WitImport.Tables.Defs
public import Silmaril.Wasi.Versions.WitImport.NetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.Http3Table.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables29.Defs

@[expose] public section

/-!
# Kernel-checked imports of `wasi:sockets@0.2.12`

The environment, worlds and package of `KC.sock2` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.sock2.importKD` (the kernel importer `importKD` on the files without doc comments), and
`sock2T_kernel_nodoc`, `sock2P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `sock2T` is the table of `KC.sock2.out`. -/
theorem KC.sock2.tableEq : table false KC.sock2.out = sock2T := by decide +kernel

/-- **`sock2T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem sock2T_kernel_nodoc : kTable false false [KF.v2.sock.network.src, KF.v2.sock.instance_network.src, KF.v2.sock.tcp.src, KF.v2.sock.tcp_create_socket.src, KF.v2.sock.udp.src, KF.v2.sock.udp_create_socket.src, KF.v2.sock.ip_name_lookup.src, KF.v2.clocks.monotonic_clock.src, KF.v2.clocks.wall_clock.src, KF.v2.clocks.timezone.src, KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some sock2T :=
  (kTable_of KC.sock2.importKD).trans (congrArg some KC.sock2.tableEq)

/-- `sock2P` is the resolved package of `KC.sock2.out`. -/
theorem KC.sock2.rpkgEq : (rtable false KC.sock2.out, envOf KC.sock2.out KC.sock2.deps) = sock2P := by decide +kernel

/-- **`sock2P` is kernel-checked** (without doc comments): table and type environment. -/
theorem sock2P_kernel_nodoc : kRPkg false false [KF.v2.sock.network.src, KF.v2.sock.instance_network.src, KF.v2.sock.tcp.src, KF.v2.sock.tcp_create_socket.src, KF.v2.sock.udp.src, KF.v2.sock.udp_create_socket.src, KF.v2.sock.ip_name_lookup.src, KF.v2.clocks.monotonic_clock.src, KF.v2.clocks.wall_clock.src, KF.v2.clocks.timezone.src, KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some sock2P :=
  (kRPkg_of KC.sock2.importKD).trans (congrArg some KC.sock2.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
