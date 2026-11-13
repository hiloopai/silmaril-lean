module

public import Silmaril.Wasi.Versions.WitImport.KCert.Http3.Elab.Thms
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
# Kernel-checked imports of `wasi:http@0.3.2`

The environment, worlds and package of `KC.http3` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.http3.importKD` (the kernel importer `importKD` on the files without doc comments), and
`http3T_kernel_nodoc`, `http3P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `http3T` is the table of `KC.http3.out`. -/
theorem KC.http3.tableEq : table true KC.http3.out = http3T := by decide +kernel

/-- **`http3T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem http3T_kernel_nodoc : kTable true true [KF.v3.http.worlds.src, KF.v3.http.types.src, KF.v3.clocks.monotonic_clock.src, KF.v3.clocks.system_clock.src, KF.v3.clocks.timezone.src, KF.v3.clocks.types.src] = some http3T :=
  (kTable_of KC.http3.importKD).trans (congrArg some KC.http3.tableEq)

/-- `http3P` is the resolved package of `KC.http3.out`. -/
theorem KC.http3.rpkgEq : (rtable true KC.http3.out, envOf KC.http3.out KC.http3.deps) = http3P := by decide +kernel

/-- **`http3P` is kernel-checked** (without doc comments): table and type environment. -/
theorem http3P_kernel_nodoc : kRPkg true true [KF.v3.http.worlds.src, KF.v3.http.types.src, KF.v3.clocks.monotonic_clock.src, KF.v3.clocks.system_clock.src, KF.v3.clocks.timezone.src, KF.v3.clocks.types.src] = some http3P :=
  (kRPkg_of KC.http3.importKD).trans (congrArg some KC.http3.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
