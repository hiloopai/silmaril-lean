module

public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks2.Elab.Thms
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
# Kernel-checked imports of `wasi:clocks@0.2.12`

The environment, worlds and package of `KC.clocks2` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.clocks2.importKD` (the kernel importer `importKD` on the files without doc comments), and
`clocks2T_kernel_nodoc`, `clocks2P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `clocks2T` is the table of `KC.clocks2.out`. -/
theorem KC.clocks2.tableEq : table false KC.clocks2.out = clocks2T := by decide +kernel

/-- **`clocks2T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem clocks2T_kernel_nodoc : kTable false false [KF.v2.clocks.monotonic_clock.src, KF.v2.clocks.wall_clock.src, KF.v2.clocks.timezone.src, KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some clocks2T :=
  (kTable_of KC.clocks2.importKD).trans (congrArg some KC.clocks2.tableEq)

/-- `clocks2P` is the resolved package of `KC.clocks2.out`. -/
theorem KC.clocks2.rpkgEq : (rtable false KC.clocks2.out, envOf KC.clocks2.out KC.clocks2.deps) = clocks2P := by decide +kernel

/-- **`clocks2P` is kernel-checked** (without doc comments): table and type environment. -/
theorem clocks2P_kernel_nodoc : kRPkg false false [KF.v2.clocks.monotonic_clock.src, KF.v2.clocks.wall_clock.src, KF.v2.clocks.timezone.src, KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some clocks2P :=
  (kRPkg_of KC.clocks2.importKD).trans (congrArg some KC.clocks2.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
