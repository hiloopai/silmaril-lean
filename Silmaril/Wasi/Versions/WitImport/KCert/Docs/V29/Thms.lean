module

public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V29Cli.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V29Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V29Fs.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V29Fs2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V29Http.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V29Http2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V29Io.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V29Rand.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V29Sock.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V29Sock2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V29Sock3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Io29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Cli29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Fs29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Rand29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Sock29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Http29.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Thms

@[expose] public section

/-!
# Kernel-checked imports of WASI 0.2.9 on the vendored files, doc comments parsed

For each table, drop list and resolved package of `KCert/*`: `<x>_kernel`, the importer
evaluated in the kernel (`kTable`, `kDrops`, `kRPkg`, `Silmaril.Wasi.Versions.WitImport.KImport`,
`KSplit`) on the glued texts with their doc comments (`KF.….full`, `wit_src%`), every token
parsed, gives it. From the certificates on the texts without doc comments (`KC.….importKD`),
the per-file kernel checks `KF.….parseEr` (`KCert/Erase/*`: the parse with doc comments, erased,
is the parse without them) and `kTable_of_erase`, `kDrops_of_erase`, `kRPkg_of_erase`
(`Silmaril.Wasi.Versions.WitImport.KErase`: doc comments cannot change a table, a drop list or a
resolved package).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- **`io29P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem io29P_kernel : kRPkg false false
    [KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some io29P :=
  (kRPkg_of_erase (.cons KF.v29.io.error.parseEr (.cons KF.v29.io.poll.parseEr (.cons KF.v29.io.streams.parseEr .nil))) KC.io29.importKD).trans (congrArg some KC.io29.rpkgEq)


/-- **`clocks29P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem clocks29P_kernel : kRPkg false false
    [KF.v29.clocks.monotonic_clock.full, KF.v29.clocks.wall_clock.full, KF.v29.clocks.timezone.full, KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some clocks29P :=
  (kRPkg_of_erase (.cons KF.v29.clocks.monotonic_clock.parseEr (.cons KF.v29.clocks.wall_clock.parseEr (.cons KF.v29.clocks.timezone.parseEr (.cons KF.v29.io.error.parseEr (.cons KF.v29.io.poll.parseEr (.cons KF.v29.io.streams.parseEr .nil)))))) KC.clocks29.importKD).trans (congrArg some KC.clocks29.rpkgEq)


/-- **`cli29P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem cli29P_kernel : kRPkg false false
    [KF.v29.cli.environment.full, KF.v29.cli.exit.full, KF.v29.cli.run.full, KF.v29.cli.stdio.full, KF.v29.cli.terminal.full, KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some cli29P :=
  (kRPkg_of_erase (.cons KF.v29.cli.environment.parseEr (.cons KF.v29.cli.exit.parseEr (.cons KF.v29.cli.run.parseEr (.cons KF.v29.cli.stdio.parseEr (.cons KF.v29.cli.terminal.parseEr (.cons KF.v29.io.error.parseEr (.cons KF.v29.io.poll.parseEr (.cons KF.v29.io.streams.parseEr .nil)))))))) KC.cli29.importKD).trans (congrArg some KC.cli29.rpkgEq)


/-- **`fs29P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem fs29P_kernel : kRPkg false false
    [KF.v29.fs.types.full, KF.v29.fs.preopens.full, KF.v29.clocks.monotonic_clock.full, KF.v29.clocks.wall_clock.full, KF.v29.clocks.timezone.full, KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some fs29P :=
  (kRPkg_of_erase (.cons KF.v29.fs.types.parseEr (.cons KF.v29.fs.preopens.parseEr (.cons KF.v29.clocks.monotonic_clock.parseEr (.cons KF.v29.clocks.wall_clock.parseEr (.cons KF.v29.clocks.timezone.parseEr (.cons KF.v29.io.error.parseEr (.cons KF.v29.io.poll.parseEr (.cons KF.v29.io.streams.parseEr .nil)))))))) KC.fs29.importKD).trans (congrArg some KC.fs29.rpkgEq)


/-- **`rand29P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem rand29P_kernel : kRPkg false false
    [KF.v29.rand.insecure_seed.full, KF.v29.rand.insecure.full, KF.v29.rand.random.full] =
    some rand29P :=
  (kRPkg_of_erase (.cons KF.v29.rand.insecure_seed.parseEr (.cons KF.v29.rand.insecure.parseEr (.cons KF.v29.rand.random.parseEr .nil))) KC.rand29.importKD).trans (congrArg some KC.rand29.rpkgEq)


/-- **`sock29P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem sock29P_kernel : kRPkg false false
    [KF.v29.sock.network.full, KF.v29.sock.instance_network.full, KF.v29.sock.tcp.full, KF.v29.sock.tcp_create_socket.full, KF.v29.sock.udp.full, KF.v29.sock.udp_create_socket.full, KF.v29.sock.ip_name_lookup.full, KF.v29.clocks.monotonic_clock.full, KF.v29.clocks.wall_clock.full, KF.v29.clocks.timezone.full, KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some sock29P :=
  (kRPkg_of_erase (.cons KF.v29.sock.network.parseEr (.cons KF.v29.sock.instance_network.parseEr (.cons KF.v29.sock.tcp.parseEr (.cons KF.v29.sock.tcp_create_socket.parseEr (.cons KF.v29.sock.udp.parseEr (.cons KF.v29.sock.udp_create_socket.parseEr (.cons KF.v29.sock.ip_name_lookup.parseEr (.cons KF.v29.clocks.monotonic_clock.parseEr (.cons KF.v29.clocks.wall_clock.parseEr (.cons KF.v29.clocks.timezone.parseEr (.cons KF.v29.io.error.parseEr (.cons KF.v29.io.poll.parseEr (.cons KF.v29.io.streams.parseEr .nil))))))))))))) KC.sock29.importKD).trans (congrArg some KC.sock29.rpkgEq)


/-- **`http29P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem http29P_kernel : kRPkg false false
    [KF.v29.http.types.full, KF.v29.http.handler.full, KF.v29.clocks.monotonic_clock.full, KF.v29.clocks.wall_clock.full, KF.v29.clocks.timezone.full, KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some http29P :=
  (kRPkg_of_erase (.cons KF.v29.http.types.parseEr (.cons KF.v29.http.handler.parseEr (.cons KF.v29.clocks.monotonic_clock.parseEr (.cons KF.v29.clocks.wall_clock.parseEr (.cons KF.v29.clocks.timezone.parseEr (.cons KF.v29.io.error.parseEr (.cons KF.v29.io.poll.parseEr (.cons KF.v29.io.streams.parseEr .nil)))))))) KC.http29.importKD).trans (congrArg some KC.http29.rpkgEq)

end Silmaril.Wasi.Versions.WitImport
