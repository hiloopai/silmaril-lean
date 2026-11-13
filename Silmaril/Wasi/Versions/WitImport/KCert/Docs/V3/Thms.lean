module

public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V3Cli.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V3Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V3Fs.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V3Fs2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V3Http.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V3Http2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V3Rand.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V3Sock.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Erase.V3Sock2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Rand3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Cli3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Fs3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Sock3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Http3.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Thms

@[expose] public section

/-!
# Kernel-checked imports of WASI 0.3.2 on the vendored files, doc comments parsed

For each table, drop list and resolved package of `KCert/*`: `<x>_kernel`, the importer
evaluated in the kernel (`kTable`, `kDrops`, `kRPkg`, `Silmaril.Wasi.Versions.WitImport.KImport`,
`KSplit`) on the glued texts with their doc comments (`KF.….full`, `wit_src%`), every token
parsed, gives it. From the certificates on the texts without doc comments (`KC.….importKD`),
the per-file kernel checks `KF.….parseEr` (`KCert/Erase/*`: the parse with doc comments, erased,
is the parse without them) and `kTable_of_erase`, `kDrops_of_erase`, `kRPkg_of_erase`
(`Silmaril.Wasi.Versions.WitImport.KErase`: doc comments cannot change a table, a drop list or a
resolved package).

The tables `rand3T`, `cli3T` and `clocks3T` have their `_kernel` theorems in
`KTables/*` (the whole importer evaluated in the kernel, follow-up 4).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- **`rand3P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem rand3P_kernel : kRPkg true false
    [KF.v3.rand.insecure_seed.full, KF.v3.rand.insecure.full, KF.v3.rand.random.full] =
    some rand3P :=
  (kRPkg_of_erase (.cons KF.v3.rand.insecure_seed.parseEr (.cons KF.v3.rand.insecure.parseEr (.cons KF.v3.rand.random.parseEr .nil))) KC.rand3.importKD).trans (congrArg some KC.rand3.rpkgEq)


/-- **`clocks3P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem clocks3P_kernel : kRPkg true false
    [KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some clocks3P :=
  (kRPkg_of_erase (.cons KF.v3.clocks.monotonic_clock.parseEr (.cons KF.v3.clocks.system_clock.parseEr (.cons KF.v3.clocks.timezone.parseEr (.cons KF.v3.clocks.types.parseEr .nil)))) KC.clocks3.importKD).trans (congrArg some KC.clocks3.rpkgEq)


/-- **`cli3P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem cli3P_kernel : kRPkg true false
    [KF.v3.cli.environment.full, KF.v3.cli.exit.full, KF.v3.cli.run.full, KF.v3.cli.stdio.full, KF.v3.cli.terminal.full] =
    some cli3P :=
  (kRPkg_of_erase (.cons KF.v3.cli.environment.parseEr (.cons KF.v3.cli.exit.parseEr (.cons KF.v3.cli.run.parseEr (.cons KF.v3.cli.stdio.parseEr (.cons KF.v3.cli.terminal.parseEr .nil))))) KC.cli3.importKD).trans (congrArg some KC.cli3.rpkgEq)


/-- **`fs3T`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem fs3T_kernel : kTable true false
    [KF.v3.fs.types.full, KF.v3.fs.preopens.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some fs3T :=
  (kTable_of_erase (.cons KF.v3.fs.types.parseEr (.cons KF.v3.fs.preopens.parseEr (.cons KF.v3.clocks.monotonic_clock.parseEr (.cons KF.v3.clocks.system_clock.parseEr (.cons KF.v3.clocks.timezone.parseEr (.cons KF.v3.clocks.types.parseEr .nil)))))) KC.fs3.importKD).trans (congrArg some KC.fs3.tableEq)


/-- **`fs3D`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem fs3D_kernel : kDrops true
    [KF.v3.fs.types.full, KF.v3.fs.preopens.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some fs3D :=
  (kDrops_of_erase (.cons KF.v3.fs.types.parseEr (.cons KF.v3.fs.preopens.parseEr (.cons KF.v3.clocks.monotonic_clock.parseEr (.cons KF.v3.clocks.system_clock.parseEr (.cons KF.v3.clocks.timezone.parseEr (.cons KF.v3.clocks.types.parseEr .nil)))))) KC.fs3.importKD).trans (congrArg some KC.fs3.dropsEq)


/-- **`fs3P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem fs3P_kernel : kRPkg true false
    [KF.v3.fs.types.full, KF.v3.fs.preopens.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some fs3P :=
  (kRPkg_of_erase (.cons KF.v3.fs.types.parseEr (.cons KF.v3.fs.preopens.parseEr (.cons KF.v3.clocks.monotonic_clock.parseEr (.cons KF.v3.clocks.system_clock.parseEr (.cons KF.v3.clocks.timezone.parseEr (.cons KF.v3.clocks.types.parseEr .nil)))))) KC.fs3.importKD).trans (congrArg some KC.fs3.rpkgEq)


/-- **`sock3T`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem sock3T_kernel : kTable true false
    [KF.v3.sock.types.full, KF.v3.sock.ip_name_lookup.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some sock3T :=
  (kTable_of_erase (.cons KF.v3.sock.types.parseEr (.cons KF.v3.sock.ip_name_lookup.parseEr (.cons KF.v3.clocks.monotonic_clock.parseEr (.cons KF.v3.clocks.system_clock.parseEr (.cons KF.v3.clocks.timezone.parseEr (.cons KF.v3.clocks.types.parseEr .nil)))))) KC.sock3.importKD).trans (congrArg some KC.sock3.tableEq)


/-- **`sock3P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem sock3P_kernel : kRPkg true false
    [KF.v3.sock.types.full, KF.v3.sock.ip_name_lookup.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some sock3P :=
  (kRPkg_of_erase (.cons KF.v3.sock.types.parseEr (.cons KF.v3.sock.ip_name_lookup.parseEr (.cons KF.v3.clocks.monotonic_clock.parseEr (.cons KF.v3.clocks.system_clock.parseEr (.cons KF.v3.clocks.timezone.parseEr (.cons KF.v3.clocks.types.parseEr .nil)))))) KC.sock3.importKD).trans (congrArg some KC.sock3.rpkgEq)


/-- **`http3T`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem http3T_kernel : kTable true true
    [KF.v3.http.worlds.full, KF.v3.http.types.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some http3T :=
  (kTable_of_erase (.cons KF.v3.http.worlds.parseEr (.cons KF.v3.http.types.parseEr (.cons KF.v3.clocks.monotonic_clock.parseEr (.cons KF.v3.clocks.system_clock.parseEr (.cons KF.v3.clocks.timezone.parseEr (.cons KF.v3.clocks.types.parseEr .nil)))))) KC.http3.importKD).trans (congrArg some KC.http3.tableEq)


/-- **`http3P`**: the kernel importer on the vendored files, doc comments parsed. -/
theorem http3P_kernel : kRPkg true true
    [KF.v3.http.worlds.full, KF.v3.http.types.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some http3P :=
  (kRPkg_of_erase (.cons KF.v3.http.worlds.parseEr (.cons KF.v3.http.types.parseEr (.cons KF.v3.clocks.monotonic_clock.parseEr (.cons KF.v3.clocks.system_clock.parseEr (.cons KF.v3.clocks.timezone.parseEr (.cons KF.v3.clocks.types.parseEr .nil)))))) KC.http3.importKD).trans (congrArg some KC.http3.rpkgEq)

end Silmaril.Wasi.Versions.WitImport
