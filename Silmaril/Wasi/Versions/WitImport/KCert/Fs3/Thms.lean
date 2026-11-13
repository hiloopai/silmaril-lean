module

public import Silmaril.Wasi.Versions.WitImport.KCert.Fs3.Elab.Thms
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
# Kernel-checked imports of `wasi:filesystem@0.3.2`

The environment, worlds and package of `KC.fs3` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.fs3.importKD` (the kernel importer `importKD` on the files without doc comments), and
`fs3T_kernel_nodoc`, `fs3D_kernel_nodoc`, `fs3P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `fs3T` is the table of `KC.fs3.out`. -/
theorem KC.fs3.tableEq : table true KC.fs3.out = fs3T := by decide +kernel

/-- **`fs3T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem fs3T_kernel_nodoc : kTable true false [KF.v3.fs.types.src, KF.v3.fs.preopens.src, KF.v3.clocks.monotonic_clock.src, KF.v3.clocks.system_clock.src, KF.v3.clocks.timezone.src, KF.v3.clocks.types.src] = some fs3T :=
  (kTable_of KC.fs3.importKD).trans (congrArg some KC.fs3.tableEq)

/-- `fs3D` are the drops of `KC.fs3.out`. -/
theorem KC.fs3.dropsEq : drops true KC.fs3.out = fs3D := by decide +kernel

/-- **`fs3D` is kernel-checked** (without doc comments). -/
theorem fs3D_kernel_nodoc : kDrops true [KF.v3.fs.types.src, KF.v3.fs.preopens.src, KF.v3.clocks.monotonic_clock.src, KF.v3.clocks.system_clock.src, KF.v3.clocks.timezone.src, KF.v3.clocks.types.src] = some fs3D :=
  (kDrops_of KC.fs3.importKD).trans (congrArg some KC.fs3.dropsEq)

/-- `fs3P` is the resolved package of `KC.fs3.out`. -/
theorem KC.fs3.rpkgEq : (rtable true KC.fs3.out, envOf KC.fs3.out KC.fs3.deps) = fs3P := by decide +kernel

/-- **`fs3P` is kernel-checked** (without doc comments): table and type environment. -/
theorem fs3P_kernel_nodoc : kRPkg true false [KF.v3.fs.types.src, KF.v3.fs.preopens.src, KF.v3.clocks.monotonic_clock.src, KF.v3.clocks.system_clock.src, KF.v3.clocks.timezone.src, KF.v3.clocks.types.src] = some fs3P :=
  (kRPkg_of KC.fs3.importKD).trans (congrArg some KC.fs3.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
