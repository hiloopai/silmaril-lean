module

public import Silmaril.Wasi.Versions.WitImport.KCert.Sock29.Elab.Thms
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
# Kernel-checked imports of `wasi:sockets@0.2.9`

The environment, worlds and package of `KC.sock29` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.sock29.importKD` (the kernel importer `importKD` on the files without doc comments), and
`sock29P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `sock29P` is the resolved package of `KC.sock29.out`. -/
theorem KC.sock29.rpkgEq : (rtable false KC.sock29.out, envOf KC.sock29.out KC.sock29.deps) = sock29P := by decide +kernel

/-- **`sock29P` is kernel-checked** (without doc comments): table and type environment. -/
theorem sock29P_kernel_nodoc : kRPkg false false [KF.v29.sock.network.src, KF.v29.sock.instance_network.src, KF.v29.sock.tcp.src, KF.v29.sock.tcp_create_socket.src, KF.v29.sock.udp.src, KF.v29.sock.udp_create_socket.src, KF.v29.sock.ip_name_lookup.src, KF.v29.clocks.monotonic_clock.src, KF.v29.clocks.wall_clock.src, KF.v29.clocks.timezone.src, KF.v29.io.error.src, KF.v29.io.poll.src, KF.v29.io.streams.src] = some sock29P :=
  (kRPkg_of KC.sock29.importKD).trans (congrArg some KC.sock29.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
