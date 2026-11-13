module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Cli.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Fs.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Fs2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Http.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Http2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Io.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Rand.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Sock.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Sock2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V29Sock3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Io29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Cli29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Fs29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Rand29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Sock29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Http29.Thms
public import Silmaril.Wasi.Versions.WitImport.KTokens.Thms

@[expose] public section

/-!
# Kernel-checked imports of WASI 0.2.9 on the vendored files' tokens

For each table, drop list and resolved package of `KCert/*`: `<x>_kernel_tokens`, the importer
evaluated in the kernel (`kTableTok`, `kDropsTok`, `kRPkgTok`, `Silmaril.Wasi.Versions.WitImport.KTokens`)
on the glued texts with their doc comments (`KF.….full`, `wit_src%`), whose doc-comment tokens
are dropped after lexing, gives it. From `<x>_kernel_nodoc` and the per-file `KF.….parseNd`
(`KCert/Lex/*`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- **`io29P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem io29P_kernel_tokens : kRPkgTok false false
    [KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some io29P :=
  (kRPkgTok_of (.cons KF.v29.io.error.parseNd (.cons KF.v29.io.poll.parseNd (.cons KF.v29.io.streams.parseNd .nil))) KC.io29.importKD).trans (congrArg some KC.io29.rpkgEq)

/-- **`clocks29P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem clocks29P_kernel_tokens : kRPkgTok false false
    [KF.v29.clocks.monotonic_clock.full, KF.v29.clocks.wall_clock.full, KF.v29.clocks.timezone.full, KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some clocks29P :=
  (kRPkgTok_of (.cons KF.v29.clocks.monotonic_clock.parseNd (.cons KF.v29.clocks.wall_clock.parseNd (.cons KF.v29.clocks.timezone.parseNd (.cons KF.v29.io.error.parseNd (.cons KF.v29.io.poll.parseNd (.cons KF.v29.io.streams.parseNd .nil)))))) KC.clocks29.importKD).trans (congrArg some KC.clocks29.rpkgEq)

/-- **`cli29P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem cli29P_kernel_tokens : kRPkgTok false false
    [KF.v29.cli.environment.full, KF.v29.cli.exit.full, KF.v29.cli.run.full, KF.v29.cli.stdio.full, KF.v29.cli.terminal.full, KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some cli29P :=
  (kRPkgTok_of (.cons KF.v29.cli.environment.parseNd (.cons KF.v29.cli.exit.parseNd (.cons KF.v29.cli.run.parseNd (.cons KF.v29.cli.stdio.parseNd (.cons KF.v29.cli.terminal.parseNd (.cons KF.v29.io.error.parseNd (.cons KF.v29.io.poll.parseNd (.cons KF.v29.io.streams.parseNd .nil)))))))) KC.cli29.importKD).trans (congrArg some KC.cli29.rpkgEq)

/-- **`fs29P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem fs29P_kernel_tokens : kRPkgTok false false
    [KF.v29.fs.types.full, KF.v29.fs.preopens.full, KF.v29.clocks.monotonic_clock.full, KF.v29.clocks.wall_clock.full, KF.v29.clocks.timezone.full, KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some fs29P :=
  (kRPkgTok_of (.cons KF.v29.fs.types.parseNd (.cons KF.v29.fs.preopens.parseNd (.cons KF.v29.clocks.monotonic_clock.parseNd (.cons KF.v29.clocks.wall_clock.parseNd (.cons KF.v29.clocks.timezone.parseNd (.cons KF.v29.io.error.parseNd (.cons KF.v29.io.poll.parseNd (.cons KF.v29.io.streams.parseNd .nil)))))))) KC.fs29.importKD).trans (congrArg some KC.fs29.rpkgEq)

/-- **`rand29P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem rand29P_kernel_tokens : kRPkgTok false false
    [KF.v29.rand.insecure_seed.full, KF.v29.rand.insecure.full, KF.v29.rand.random.full] =
    some rand29P :=
  (kRPkgTok_of (.cons KF.v29.rand.insecure_seed.parseNd (.cons KF.v29.rand.insecure.parseNd (.cons KF.v29.rand.random.parseNd .nil))) KC.rand29.importKD).trans (congrArg some KC.rand29.rpkgEq)

/-- **`sock29P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem sock29P_kernel_tokens : kRPkgTok false false
    [KF.v29.sock.network.full, KF.v29.sock.instance_network.full, KF.v29.sock.tcp.full, KF.v29.sock.tcp_create_socket.full, KF.v29.sock.udp.full, KF.v29.sock.udp_create_socket.full, KF.v29.sock.ip_name_lookup.full, KF.v29.clocks.monotonic_clock.full, KF.v29.clocks.wall_clock.full, KF.v29.clocks.timezone.full, KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some sock29P :=
  (kRPkgTok_of (.cons KF.v29.sock.network.parseNd (.cons KF.v29.sock.instance_network.parseNd (.cons KF.v29.sock.tcp.parseNd (.cons KF.v29.sock.tcp_create_socket.parseNd (.cons KF.v29.sock.udp.parseNd (.cons KF.v29.sock.udp_create_socket.parseNd (.cons KF.v29.sock.ip_name_lookup.parseNd (.cons KF.v29.clocks.monotonic_clock.parseNd (.cons KF.v29.clocks.wall_clock.parseNd (.cons KF.v29.clocks.timezone.parseNd (.cons KF.v29.io.error.parseNd (.cons KF.v29.io.poll.parseNd (.cons KF.v29.io.streams.parseNd .nil))))))))))))) KC.sock29.importKD).trans (congrArg some KC.sock29.rpkgEq)

/-- **`http29P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem http29P_kernel_tokens : kRPkgTok false false
    [KF.v29.http.types.full, KF.v29.http.handler.full, KF.v29.clocks.monotonic_clock.full, KF.v29.clocks.wall_clock.full, KF.v29.clocks.timezone.full, KF.v29.io.error.full, KF.v29.io.poll.full, KF.v29.io.streams.full] =
    some http29P :=
  (kRPkgTok_of (.cons KF.v29.http.types.parseNd (.cons KF.v29.http.handler.parseNd (.cons KF.v29.clocks.monotonic_clock.parseNd (.cons KF.v29.clocks.wall_clock.parseNd (.cons KF.v29.clocks.timezone.parseNd (.cons KF.v29.io.error.parseNd (.cons KF.v29.io.poll.parseNd (.cons KF.v29.io.streams.parseNd .nil)))))))) KC.http29.importKD).trans (congrArg some KC.http29.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
