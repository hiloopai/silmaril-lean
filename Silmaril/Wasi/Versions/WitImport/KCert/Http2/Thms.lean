module

public import Silmaril.Wasi.Versions.WitImport.KCert.Http2.Elab.Thms
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
# Kernel-checked imports of `wasi:http@0.2.12`

The environment, worlds and package of `KC.http2` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.http2.importKD` (the kernel importer `importKD` on the files without doc comments), and
`http2T_kernel_nodoc`, `http2P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `http2T` is the table of `KC.http2.out`. -/
theorem KC.http2.tableEq : table false KC.http2.out = http2T := by decide +kernel

/-- **`http2T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem http2T_kernel_nodoc : kTable false false [KF.v2.http.types.src, KF.v2.http.handler.src, KF.v2.clocks.monotonic_clock.src, KF.v2.clocks.wall_clock.src, KF.v2.clocks.timezone.src, KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some http2T :=
  (kTable_of KC.http2.importKD).trans (congrArg some KC.http2.tableEq)

/-- `http2P` is the resolved package of `KC.http2.out`. -/
theorem KC.http2.rpkgEq : (rtable false KC.http2.out, envOf KC.http2.out KC.http2.deps) = http2P := by decide +kernel

/-- **`http2P` is kernel-checked** (without doc comments): table and type environment. -/
theorem http2P_kernel_nodoc : kRPkg false false [KF.v2.http.types.src, KF.v2.http.handler.src, KF.v2.clocks.monotonic_clock.src, KF.v2.clocks.wall_clock.src, KF.v2.clocks.timezone.src, KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some http2P :=
  (kRPkg_of KC.http2.importKD).trans (congrArg some KC.http2.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
