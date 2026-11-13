module

public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Cli.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Fs.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Fs2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Http.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Http2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Io.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Rand.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Sock.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Sock2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Lex.V2Sock3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Io2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Cli2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Fs2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Sock2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Http2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Rand2.Thms
public import Silmaril.Wasi.Versions.WitImport.KTokens.Thms

@[expose] public section

/-!
# Kernel-checked imports of WASI 0.2.12 on the vendored files' tokens

For each table, drop list and resolved package of `KCert/*`: `<x>_kernel_tokens`, the importer
evaluated in the kernel (`kTableTok`, `kDropsTok`, `kRPkgTok`, `Silmaril.Wasi.Versions.WitImport.KTokens`)
on the glued texts with their doc comments (`KF.….full`, `wit_src%`), whose doc-comment tokens
are dropped after lexing, gives it. From `<x>_kernel_nodoc` and the per-file `KF.….parseNd`
(`KCert/Lex/*`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- **`io2T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem io2T_kernel_tokens : kTableTok false false
    [KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some io2T :=
  (kTableTok_of (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil))) KC.io2.importKD).trans (congrArg some KC.io2.tableEq)

/-- **`io2D`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem io2D_kernel_tokens : kDropsTok false
    [KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some io2D :=
  (kDropsTok_of (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil))) KC.io2.importKD).trans (congrArg some KC.io2.dropsEq)

/-- **`io2P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem io2P_kernel_tokens : kRPkgTok false false
    [KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some io2P :=
  (kRPkgTok_of (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil))) KC.io2.importKD).trans (congrArg some KC.io2.rpkgEq)

/-- **`clocks2T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem clocks2T_kernel_tokens : kTableTok false false
    [KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some clocks2T :=
  (kTableTok_of (.cons KF.v2.clocks.monotonic_clock.parseNd (.cons KF.v2.clocks.wall_clock.parseNd (.cons KF.v2.clocks.timezone.parseNd (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil)))))) KC.clocks2.importKD).trans (congrArg some KC.clocks2.tableEq)

/-- **`clocks2P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem clocks2P_kernel_tokens : kRPkgTok false false
    [KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some clocks2P :=
  (kRPkgTok_of (.cons KF.v2.clocks.monotonic_clock.parseNd (.cons KF.v2.clocks.wall_clock.parseNd (.cons KF.v2.clocks.timezone.parseNd (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil)))))) KC.clocks2.importKD).trans (congrArg some KC.clocks2.rpkgEq)

/-- **`cli2T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem cli2T_kernel_tokens : kTableTok false false
    [KF.v2.cli.environment.full, KF.v2.cli.exit.full, KF.v2.cli.run.full, KF.v2.cli.stdio.full, KF.v2.cli.terminal.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some cli2T :=
  (kTableTok_of (.cons KF.v2.cli.environment.parseNd (.cons KF.v2.cli.exit.parseNd (.cons KF.v2.cli.run.parseNd (.cons KF.v2.cli.stdio.parseNd (.cons KF.v2.cli.terminal.parseNd (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil)))))))) KC.cli2.importKD).trans (congrArg some KC.cli2.tableEq)

/-- **`cli2P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem cli2P_kernel_tokens : kRPkgTok false false
    [KF.v2.cli.environment.full, KF.v2.cli.exit.full, KF.v2.cli.run.full, KF.v2.cli.stdio.full, KF.v2.cli.terminal.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some cli2P :=
  (kRPkgTok_of (.cons KF.v2.cli.environment.parseNd (.cons KF.v2.cli.exit.parseNd (.cons KF.v2.cli.run.parseNd (.cons KF.v2.cli.stdio.parseNd (.cons KF.v2.cli.terminal.parseNd (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil)))))))) KC.cli2.importKD).trans (congrArg some KC.cli2.rpkgEq)

/-- **`fs2T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem fs2T_kernel_tokens : kTableTok false false
    [KF.v2.fs.types.full, KF.v2.fs.preopens.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some fs2T :=
  (kTableTok_of (.cons KF.v2.fs.types.parseNd (.cons KF.v2.fs.preopens.parseNd (.cons KF.v2.clocks.monotonic_clock.parseNd (.cons KF.v2.clocks.wall_clock.parseNd (.cons KF.v2.clocks.timezone.parseNd (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil)))))))) KC.fs2.importKD).trans (congrArg some KC.fs2.tableEq)

/-- **`fs2D`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem fs2D_kernel_tokens : kDropsTok false
    [KF.v2.fs.types.full, KF.v2.fs.preopens.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some fs2D :=
  (kDropsTok_of (.cons KF.v2.fs.types.parseNd (.cons KF.v2.fs.preopens.parseNd (.cons KF.v2.clocks.monotonic_clock.parseNd (.cons KF.v2.clocks.wall_clock.parseNd (.cons KF.v2.clocks.timezone.parseNd (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil)))))))) KC.fs2.importKD).trans (congrArg some KC.fs2.dropsEq)

/-- **`fs2P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem fs2P_kernel_tokens : kRPkgTok false false
    [KF.v2.fs.types.full, KF.v2.fs.preopens.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some fs2P :=
  (kRPkgTok_of (.cons KF.v2.fs.types.parseNd (.cons KF.v2.fs.preopens.parseNd (.cons KF.v2.clocks.monotonic_clock.parseNd (.cons KF.v2.clocks.wall_clock.parseNd (.cons KF.v2.clocks.timezone.parseNd (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil)))))))) KC.fs2.importKD).trans (congrArg some KC.fs2.rpkgEq)

/-- **`sock2T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem sock2T_kernel_tokens : kTableTok false false
    [KF.v2.sock.network.full, KF.v2.sock.instance_network.full, KF.v2.sock.tcp.full, KF.v2.sock.tcp_create_socket.full, KF.v2.sock.udp.full, KF.v2.sock.udp_create_socket.full, KF.v2.sock.ip_name_lookup.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some sock2T :=
  (kTableTok_of (.cons KF.v2.sock.network.parseNd (.cons KF.v2.sock.instance_network.parseNd (.cons KF.v2.sock.tcp.parseNd (.cons KF.v2.sock.tcp_create_socket.parseNd (.cons KF.v2.sock.udp.parseNd (.cons KF.v2.sock.udp_create_socket.parseNd (.cons KF.v2.sock.ip_name_lookup.parseNd (.cons KF.v2.clocks.monotonic_clock.parseNd (.cons KF.v2.clocks.wall_clock.parseNd (.cons KF.v2.clocks.timezone.parseNd (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil))))))))))))) KC.sock2.importKD).trans (congrArg some KC.sock2.tableEq)

/-- **`sock2P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem sock2P_kernel_tokens : kRPkgTok false false
    [KF.v2.sock.network.full, KF.v2.sock.instance_network.full, KF.v2.sock.tcp.full, KF.v2.sock.tcp_create_socket.full, KF.v2.sock.udp.full, KF.v2.sock.udp_create_socket.full, KF.v2.sock.ip_name_lookup.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some sock2P :=
  (kRPkgTok_of (.cons KF.v2.sock.network.parseNd (.cons KF.v2.sock.instance_network.parseNd (.cons KF.v2.sock.tcp.parseNd (.cons KF.v2.sock.tcp_create_socket.parseNd (.cons KF.v2.sock.udp.parseNd (.cons KF.v2.sock.udp_create_socket.parseNd (.cons KF.v2.sock.ip_name_lookup.parseNd (.cons KF.v2.clocks.monotonic_clock.parseNd (.cons KF.v2.clocks.wall_clock.parseNd (.cons KF.v2.clocks.timezone.parseNd (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil))))))))))))) KC.sock2.importKD).trans (congrArg some KC.sock2.rpkgEq)

/-- **`http2T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem http2T_kernel_tokens : kTableTok false false
    [KF.v2.http.types.full, KF.v2.http.handler.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some http2T :=
  (kTableTok_of (.cons KF.v2.http.types.parseNd (.cons KF.v2.http.handler.parseNd (.cons KF.v2.clocks.monotonic_clock.parseNd (.cons KF.v2.clocks.wall_clock.parseNd (.cons KF.v2.clocks.timezone.parseNd (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil)))))))) KC.http2.importKD).trans (congrArg some KC.http2.tableEq)

/-- **`http2P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem http2P_kernel_tokens : kRPkgTok false false
    [KF.v2.http.types.full, KF.v2.http.handler.full, KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full] =
    some http2P :=
  (kRPkgTok_of (.cons KF.v2.http.types.parseNd (.cons KF.v2.http.handler.parseNd (.cons KF.v2.clocks.monotonic_clock.parseNd (.cons KF.v2.clocks.wall_clock.parseNd (.cons KF.v2.clocks.timezone.parseNd (.cons KF.v2.io.error.parseNd (.cons KF.v2.io.poll.parseNd (.cons KF.v2.io.streams.parseNd .nil)))))))) KC.http2.importKD).trans (congrArg some KC.http2.rpkgEq)

/-- **`rand2T`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem rand2T_kernel_tokens : kTableTok false false
    [KF.v2.rand.insecure_seed.full, KF.v2.rand.insecure.full, KF.v2.rand.random.full] =
    some rand2T :=
  (kTableTok_of (.cons KF.v2.rand.insecure_seed.parseNd (.cons KF.v2.rand.insecure.parseNd (.cons KF.v2.rand.random.parseNd .nil))) KC.rand2.importKD).trans (congrArg some KC.rand2.tableEq)

/-- **`rand2P`**: the kernel importer on the vendored files' tokens without doc comments. -/
theorem rand2P_kernel_tokens : kRPkgTok false false
    [KF.v2.rand.insecure_seed.full, KF.v2.rand.insecure.full, KF.v2.rand.random.full] =
    some rand2P :=
  (kRPkgTok_of (.cons KF.v2.rand.insecure_seed.parseNd (.cons KF.v2.rand.insecure.parseNd (.cons KF.v2.rand.random.parseNd .nil))) KC.rand2.importKD).trans (congrArg some KC.rand2.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
