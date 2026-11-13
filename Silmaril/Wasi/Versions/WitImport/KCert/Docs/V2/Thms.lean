module

public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V2Cli.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V2Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V2Fs.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V2Fs2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V2Http.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V2Http2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V2Io.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V2Rand.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V2Sock.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V2Sock2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V2Sock3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Io2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Cli2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Fs2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Sock2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Http2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Rand2.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Thms

@[expose] public section

/-!
# Kernel-checked imports of WASI 0.2.12 on the vendored files, doc comments parsed

For each table, drop list and resolved package of `KCert/*`: `<x>_kernel`, the importer
evaluated in the kernel (`kTable`, `kDrops`, `kRPkg`, `Silmaril.Wasi.Versions.WitImport.KImport`,
`KSplit`) on the glued texts with their doc comments (`KF.….full`, `wit_src%`), every token
parsed, gives it. From the certificates on the texts without doc comments (`KC.….importKD`),
the per-file kernel checks `KF.….parseEr` (`KCert/Erase/*`: the parse with doc comments, erased,
is the parse without them) and `kTable_of_erase`, `kDrops_of_erase`, `kRPkg_of_erase`
(`Silmaril.Wasi.Versions.WitImport.KErase`: doc comments cannot change a table, a drop list or a
resolved package).

The table `rand2T` has its `_kernel` theorem in `KTables/*` (the whole importer evaluated in the kernel, follow-up 4).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- **`io2T`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem io2T_kernel : kTable false false
    [KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some io2T :=
  (kTable_of_erase (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil))) KC.io2.importKD).trans (congrArg some KC.io2.tableEq)


/-- **`io2D`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem io2D_kernel : kDrops false
    [KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some io2D :=
  (kDrops_of_erase (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil))) KC.io2.importKD).trans (congrArg some KC.io2.dropsEq)


/-- **`io2P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem io2P_kernel : kRPkg false false
    [KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some io2P :=
  (kRPkg_of_erase (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil))) KC.io2.importKD).trans (congrArg some KC.io2.rpkgEq)


/-- **`clocks2T`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem clocks2T_kernel : kTable false false
    [KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some clocks2T :=
  (kTable_of_erase (.cons KF.v2.clocks.monotonic_clock.parseEr (.cons KF.v2.clocks.wall_clock.parseEr (.cons KF.v2.clocks.timezone.parseEr (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil)))))) KC.clocks2.importKD).trans (congrArg some KC.clocks2.tableEq)


/-- **`clocks2P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem clocks2P_kernel : kRPkg false false
    [KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some clocks2P :=
  (kRPkg_of_erase (.cons KF.v2.clocks.monotonic_clock.parseEr (.cons KF.v2.clocks.wall_clock.parseEr (.cons KF.v2.clocks.timezone.parseEr (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil)))))) KC.clocks2.importKD).trans (congrArg some KC.clocks2.rpkgEq)


/-- **`cli2T`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem cli2T_kernel : kTable false false
    [KF.v2.cli.environment.full, KF.v2.cli.exit.full, KF.v2.cli.run.full, KF.v2.cli.stdio.full, KF.v2.cli.terminal.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some cli2T :=
  (kTable_of_erase (.cons KF.v2.cli.environment.parseEr (.cons KF.v2.cli.exit.parseEr (.cons KF.v2.cli.run.parseEr (.cons KF.v2.cli.stdio.parseEr (.cons KF.v2.cli.terminal.parseEr (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil)))))))) KC.cli2.importKD).trans (congrArg some KC.cli2.tableEq)


/-- **`cli2P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem cli2P_kernel : kRPkg false false
    [KF.v2.cli.environment.full, KF.v2.cli.exit.full, KF.v2.cli.run.full, KF.v2.cli.stdio.full, KF.v2.cli.terminal.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some cli2P :=
  (kRPkg_of_erase (.cons KF.v2.cli.environment.parseEr (.cons KF.v2.cli.exit.parseEr (.cons KF.v2.cli.run.parseEr (.cons KF.v2.cli.stdio.parseEr (.cons KF.v2.cli.terminal.parseEr (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil)))))))) KC.cli2.importKD).trans (congrArg some KC.cli2.rpkgEq)


/-- **`fs2T`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem fs2T_kernel : kTable false false
    [KF.v2.fs.types.full, KF.v2.fs.preopens.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some fs2T :=
  (kTable_of_erase (.cons KF.v2.fs.types.parseEr (.cons KF.v2.fs.preopens.parseEr (.cons KF.v2.clocks.monotonic_clock.parseEr (.cons KF.v2.clocks.wall_clock.parseEr (.cons KF.v2.clocks.timezone.parseEr (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil)))))))) KC.fs2.importKD).trans (congrArg some KC.fs2.tableEq)


/-- **`fs2D`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem fs2D_kernel : kDrops false
    [KF.v2.fs.types.full, KF.v2.fs.preopens.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some fs2D :=
  (kDrops_of_erase (.cons KF.v2.fs.types.parseEr (.cons KF.v2.fs.preopens.parseEr (.cons KF.v2.clocks.monotonic_clock.parseEr (.cons KF.v2.clocks.wall_clock.parseEr (.cons KF.v2.clocks.timezone.parseEr (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil)))))))) KC.fs2.importKD).trans (congrArg some KC.fs2.dropsEq)


/-- **`fs2P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem fs2P_kernel : kRPkg false false
    [KF.v2.fs.types.full, KF.v2.fs.preopens.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some fs2P :=
  (kRPkg_of_erase (.cons KF.v2.fs.types.parseEr (.cons KF.v2.fs.preopens.parseEr (.cons KF.v2.clocks.monotonic_clock.parseEr (.cons KF.v2.clocks.wall_clock.parseEr (.cons KF.v2.clocks.timezone.parseEr (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil)))))))) KC.fs2.importKD).trans (congrArg some KC.fs2.rpkgEq)


/-- **`sock2T`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem sock2T_kernel : kTable false false
    [KF.v2.sock.network.full, KF.v2.sock.instance_network.full, KF.v2.sock.tcp.full, KF.v2.sock.tcp_create_socket.full, KF.v2.sock.udp.full, KF.v2.sock.udp_create_socket.full, KF.v2.sock.ip_name_lookup.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some sock2T :=
  (kTable_of_erase (.cons KF.v2.sock.network.parseEr (.cons KF.v2.sock.instance_network.parseEr (.cons KF.v2.sock.tcp.parseEr (.cons KF.v2.sock.tcp_create_socket.parseEr (.cons KF.v2.sock.udp.parseEr (.cons KF.v2.sock.udp_create_socket.parseEr (.cons KF.v2.sock.ip_name_lookup.parseEr (.cons KF.v2.clocks.monotonic_clock.parseEr (.cons KF.v2.clocks.wall_clock.parseEr (.cons KF.v2.clocks.timezone.parseEr (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil))))))))))))) KC.sock2.importKD).trans (congrArg some KC.sock2.tableEq)


/-- **`sock2P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem sock2P_kernel : kRPkg false false
    [KF.v2.sock.network.full, KF.v2.sock.instance_network.full, KF.v2.sock.tcp.full, KF.v2.sock.tcp_create_socket.full, KF.v2.sock.udp.full, KF.v2.sock.udp_create_socket.full, KF.v2.sock.ip_name_lookup.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some sock2P :=
  (kRPkg_of_erase (.cons KF.v2.sock.network.parseEr (.cons KF.v2.sock.instance_network.parseEr (.cons KF.v2.sock.tcp.parseEr (.cons KF.v2.sock.tcp_create_socket.parseEr (.cons KF.v2.sock.udp.parseEr (.cons KF.v2.sock.udp_create_socket.parseEr (.cons KF.v2.sock.ip_name_lookup.parseEr (.cons KF.v2.clocks.monotonic_clock.parseEr (.cons KF.v2.clocks.wall_clock.parseEr (.cons KF.v2.clocks.timezone.parseEr (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil))))))))))))) KC.sock2.importKD).trans (congrArg some KC.sock2.rpkgEq)


/-- **`http2T`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem http2T_kernel : kTable false false
    [KF.v2.http.types.full, KF.v2.http.handler.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some http2T :=
  (kTable_of_erase (.cons KF.v2.http.types.parseEr (.cons KF.v2.http.handler.parseEr (.cons KF.v2.clocks.monotonic_clock.parseEr (.cons KF.v2.clocks.wall_clock.parseEr (.cons KF.v2.clocks.timezone.parseEr (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil)))))))) KC.http2.importKD).trans (congrArg some KC.http2.tableEq)


/-- **`http2P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem http2P_kernel : kRPkg false false
    [KF.v2.http.types.full, KF.v2.http.handler.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some http2P :=
  (kRPkg_of_erase (.cons KF.v2.http.types.parseEr (.cons KF.v2.http.handler.parseEr (.cons KF.v2.clocks.monotonic_clock.parseEr (.cons KF.v2.clocks.wall_clock.parseEr (.cons KF.v2.clocks.timezone.parseEr (.cons KF.v2.io.error.parseEr (.cons KF.v2.io.poll.parseEr (.cons KF.v2.io.streams.parseEr .nil)))))))) KC.http2.importKD).trans (congrArg some KC.http2.rpkgEq)


/-- **`rand2P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem rand2P_kernel : kRPkg false false
    [KF.v2.rand.insecure_seed.full, KF.v2.rand.insecure.full, KF.v2.rand.random.full] =
    some rand2P :=
  (kRPkg_of_erase (.cons KF.v2.rand.insecure_seed.parseEr (.cons KF.v2.rand.insecure.parseEr (.cons KF.v2.rand.random.parseEr .nil))) KC.rand2.importKD).trans (congrArg some KC.rand2.rpkgEq)

end Silmaril.Wasi.Versions.WitImport
