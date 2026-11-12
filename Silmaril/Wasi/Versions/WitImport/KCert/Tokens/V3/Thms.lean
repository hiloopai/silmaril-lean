module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Cli.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Fs.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Fs2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Http.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Http2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Rand.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Sock.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V3Sock2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Rand3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Cli3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Fs3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Sock3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Http3.Thms
public import Silmaril.Wasi.Versions.WitImport.KTokens.Thms

@[expose] public section

/-!
# Kernel-checked imports of WASI 0.3.2 on the vendored files' tokens

For each table, drop list and resolved package of `KCert/*`: `<x>_kernel_tokens`, the importer
evaluated in the kernel (`kTableTok`, `kDropsTok`, `kRPkgTok`, `Silmaril.Wasi.Versions.WitImport.KTokens`)
on the glued texts with their doc comments (`KF.….full`, `wit_src%`), whose doc-comment tokens
are dropped after lexing, gives it. From `<x>_kernel_nodoc` and the per-file `KF.….parseNd`
(`KCert/Lex/*`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- **`rand3T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem rand3T_kernel_tokens : kTableTok true false
    [KF.v3.rand.insecure_seed.full, KF.v3.rand.insecure.full, KF.v3.rand.random.full] =
    some rand3T :=
  (kTableTok_of (.cons KF.v3.rand.insecure_seed.parseNd (.cons KF.v3.rand.insecure.parseNd (.cons KF.v3.rand.random.parseNd .nil))) KC.rand3.importKD).trans (congrArg some KC.rand3.tableEq)

/-- **`rand3P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem rand3P_kernel_tokens : kRPkgTok true false
    [KF.v3.rand.insecure_seed.full, KF.v3.rand.insecure.full, KF.v3.rand.random.full] =
    some rand3P :=
  (kRPkgTok_of (.cons KF.v3.rand.insecure_seed.parseNd (.cons KF.v3.rand.insecure.parseNd (.cons KF.v3.rand.random.parseNd .nil))) KC.rand3.importKD).trans (congrArg some KC.rand3.rpkgEq)

/-- **`clocks3T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem clocks3T_kernel_tokens : kTableTok true false
    [KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some clocks3T :=
  (kTableTok_of (.cons KF.v3.clocks.monotonic_clock.parseNd (.cons KF.v3.clocks.system_clock.parseNd (.cons KF.v3.clocks.timezone.parseNd (.cons KF.v3.clocks.types.parseNd .nil)))) KC.clocks3.importKD).trans (congrArg some KC.clocks3.tableEq)

/-- **`clocks3P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem clocks3P_kernel_tokens : kRPkgTok true false
    [KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some clocks3P :=
  (kRPkgTok_of (.cons KF.v3.clocks.monotonic_clock.parseNd (.cons KF.v3.clocks.system_clock.parseNd (.cons KF.v3.clocks.timezone.parseNd (.cons KF.v3.clocks.types.parseNd .nil)))) KC.clocks3.importKD).trans (congrArg some KC.clocks3.rpkgEq)

/-- **`cli3T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem cli3T_kernel_tokens : kTableTok true false
    [KF.v3.cli.environment.full, KF.v3.cli.exit.full, KF.v3.cli.run.full, KF.v3.cli.stdio.full, KF.v3.cli.terminal.full] =
    some cli3T :=
  (kTableTok_of (.cons KF.v3.cli.environment.parseNd (.cons KF.v3.cli.exit.parseNd (.cons KF.v3.cli.run.parseNd (.cons KF.v3.cli.stdio.parseNd (.cons KF.v3.cli.terminal.parseNd .nil))))) KC.cli3.importKD).trans (congrArg some KC.cli3.tableEq)

/-- **`cli3P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem cli3P_kernel_tokens : kRPkgTok true false
    [KF.v3.cli.environment.full, KF.v3.cli.exit.full, KF.v3.cli.run.full, KF.v3.cli.stdio.full, KF.v3.cli.terminal.full] =
    some cli3P :=
  (kRPkgTok_of (.cons KF.v3.cli.environment.parseNd (.cons KF.v3.cli.exit.parseNd (.cons KF.v3.cli.run.parseNd (.cons KF.v3.cli.stdio.parseNd (.cons KF.v3.cli.terminal.parseNd .nil))))) KC.cli3.importKD).trans (congrArg some KC.cli3.rpkgEq)

/-- **`fs3T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem fs3T_kernel_tokens : kTableTok true false
    [KF.v3.fs.types.full, KF.v3.fs.preopens.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some fs3T :=
  (kTableTok_of (.cons KF.v3.fs.types.parseNd (.cons KF.v3.fs.preopens.parseNd (.cons KF.v3.clocks.monotonic_clock.parseNd (.cons KF.v3.clocks.system_clock.parseNd (.cons KF.v3.clocks.timezone.parseNd (.cons KF.v3.clocks.types.parseNd .nil)))))) KC.fs3.importKD).trans (congrArg some KC.fs3.tableEq)

/-- **`fs3D`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem fs3D_kernel_tokens : kDropsTok true
    [KF.v3.fs.types.full, KF.v3.fs.preopens.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some fs3D :=
  (kDropsTok_of (.cons KF.v3.fs.types.parseNd (.cons KF.v3.fs.preopens.parseNd (.cons KF.v3.clocks.monotonic_clock.parseNd (.cons KF.v3.clocks.system_clock.parseNd (.cons KF.v3.clocks.timezone.parseNd (.cons KF.v3.clocks.types.parseNd .nil)))))) KC.fs3.importKD).trans (congrArg some KC.fs3.dropsEq)

/-- **`fs3P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem fs3P_kernel_tokens : kRPkgTok true false
    [KF.v3.fs.types.full, KF.v3.fs.preopens.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some fs3P :=
  (kRPkgTok_of (.cons KF.v3.fs.types.parseNd (.cons KF.v3.fs.preopens.parseNd (.cons KF.v3.clocks.monotonic_clock.parseNd (.cons KF.v3.clocks.system_clock.parseNd (.cons KF.v3.clocks.timezone.parseNd (.cons KF.v3.clocks.types.parseNd .nil)))))) KC.fs3.importKD).trans (congrArg some KC.fs3.rpkgEq)

/-- **`sock3T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem sock3T_kernel_tokens : kTableTok true false
    [KF.v3.sock.types.full, KF.v3.sock.ip_name_lookup.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some sock3T :=
  (kTableTok_of (.cons KF.v3.sock.types.parseNd (.cons KF.v3.sock.ip_name_lookup.parseNd (.cons KF.v3.clocks.monotonic_clock.parseNd (.cons KF.v3.clocks.system_clock.parseNd (.cons KF.v3.clocks.timezone.parseNd (.cons KF.v3.clocks.types.parseNd .nil)))))) KC.sock3.importKD).trans (congrArg some KC.sock3.tableEq)

/-- **`sock3P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem sock3P_kernel_tokens : kRPkgTok true false
    [KF.v3.sock.types.full, KF.v3.sock.ip_name_lookup.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some sock3P :=
  (kRPkgTok_of (.cons KF.v3.sock.types.parseNd (.cons KF.v3.sock.ip_name_lookup.parseNd (.cons KF.v3.clocks.monotonic_clock.parseNd (.cons KF.v3.clocks.system_clock.parseNd (.cons KF.v3.clocks.timezone.parseNd (.cons KF.v3.clocks.types.parseNd .nil)))))) KC.sock3.importKD).trans (congrArg some KC.sock3.rpkgEq)

/-- **`http3T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem http3T_kernel_tokens : kTableTok true true
    [KF.v3.http.worlds.full, KF.v3.http.types.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some http3T :=
  (kTableTok_of (.cons KF.v3.http.worlds.parseNd (.cons KF.v3.http.types.parseNd (.cons KF.v3.clocks.monotonic_clock.parseNd (.cons KF.v3.clocks.system_clock.parseNd (.cons KF.v3.clocks.timezone.parseNd (.cons KF.v3.clocks.types.parseNd .nil)))))) KC.http3.importKD).trans (congrArg some KC.http3.tableEq)

/-- **`http3P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem http3P_kernel_tokens : kRPkgTok true true
    [KF.v3.http.worlds.full, KF.v3.http.types.full, KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full] =
    some http3P :=
  (kRPkgTok_of (.cons KF.v3.http.worlds.parseNd (.cons KF.v3.http.types.parseNd (.cons KF.v3.clocks.monotonic_clock.parseNd (.cons KF.v3.clocks.system_clock.parseNd (.cons KF.v3.clocks.timezone.parseNd (.cons KF.v3.clocks.types.parseNd .nil)))))) KC.http3.importKD).trans (congrArg some KC.http3.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
