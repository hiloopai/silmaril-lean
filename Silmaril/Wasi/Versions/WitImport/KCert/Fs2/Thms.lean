module

public import Silmaril.Wasi.Versions.WitImport.KCert.Fs2.Elab.Thms
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
# Kernel-checked imports of `wasi:filesystem@0.2.12`

The environment, worlds and package of `KC.fs2` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.fs2.importKD` (the kernel importer `importKD` on the files without doc comments), and
`fs2T_kernel_nodoc`, `fs2D_kernel_nodoc`, `fs2P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `fs2T` is the table of `KC.fs2.out`. -/
theorem KC.fs2.tableEq : table false KC.fs2.out = fs2T := by decide +kernel

/-- **`fs2T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem fs2T_kernel_nodoc : kTable false false [KF.v2.fs.types.src, KF.v2.fs.preopens.src, KF.v2.clocks.monotonic_clock.src, KF.v2.clocks.wall_clock.src, KF.v2.clocks.timezone.src, KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some fs2T :=
  (kTable_of KC.fs2.importKD).trans (congrArg some KC.fs2.tableEq)

/-- `fs2D` are the drops of `KC.fs2.out`. -/
theorem KC.fs2.dropsEq : drops false KC.fs2.out = fs2D := by decide +kernel

/-- **`fs2D` is kernel-checked** (without doc comments). -/
theorem fs2D_kernel_nodoc : kDrops false [KF.v2.fs.types.src, KF.v2.fs.preopens.src, KF.v2.clocks.monotonic_clock.src, KF.v2.clocks.wall_clock.src, KF.v2.clocks.timezone.src, KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some fs2D :=
  (kDrops_of KC.fs2.importKD).trans (congrArg some KC.fs2.dropsEq)

/-- `fs2P` is the resolved package of `KC.fs2.out`. -/
theorem KC.fs2.rpkgEq : (rtable false KC.fs2.out, envOf KC.fs2.out KC.fs2.deps) = fs2P := by decide +kernel

/-- **`fs2P` is kernel-checked** (without doc comments): table and type environment. -/
theorem fs2P_kernel_nodoc : kRPkg false false [KF.v2.fs.types.src, KF.v2.fs.preopens.src, KF.v2.clocks.monotonic_clock.src, KF.v2.clocks.wall_clock.src, KF.v2.clocks.timezone.src, KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some fs2P :=
  (kRPkg_of KC.fs2.importKD).trans (congrArg some KC.fs2.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
