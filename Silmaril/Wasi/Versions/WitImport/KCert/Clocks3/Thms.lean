module

public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks3.Elab.Thms
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
# Kernel-checked imports of `wasi:clocks@0.3.2`

The environment, worlds and package of `KC.clocks3` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.clocks3.importKD` (the kernel importer `importKD` on the files without doc comments), and
`clocks3T_kernel_nodoc`, `clocks3P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `clocks3T` is the table of `KC.clocks3.out`. -/
theorem KC.clocks3.tableEq : table true KC.clocks3.out = clocks3T := by decide +kernel

/-- **`clocks3T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem clocks3T_kernel_nodoc : kTable true false [KF.v3.clocks.monotonic_clock.src, KF.v3.clocks.system_clock.src, KF.v3.clocks.timezone.src, KF.v3.clocks.types.src] = some clocks3T :=
  (kTable_of KC.clocks3.importKD).trans (congrArg some KC.clocks3.tableEq)

/-- `clocks3P` is the resolved package of `KC.clocks3.out`. -/
theorem KC.clocks3.rpkgEq : (rtable true KC.clocks3.out, envOf KC.clocks3.out KC.clocks3.deps) = clocks3P := by decide +kernel

/-- **`clocks3P` is kernel-checked** (without doc comments): table and type environment. -/
theorem clocks3P_kernel_nodoc : kRPkg true false [KF.v3.clocks.monotonic_clock.src, KF.v3.clocks.system_clock.src, KF.v3.clocks.timezone.src, KF.v3.clocks.types.src] = some clocks3P :=
  (kRPkg_of KC.clocks3.importKD).trans (congrArg some KC.clocks3.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
