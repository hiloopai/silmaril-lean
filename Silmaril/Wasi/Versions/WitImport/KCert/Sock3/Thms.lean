module

public import Silmaril.Wasi.Versions.WitImport.KCert.Sock3.Elab.Thms
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
# Kernel-checked imports of `wasi:sockets@0.3.2`

The environment, worlds and package of `KC.sock3` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.sock3.importKD` (the kernel importer `importKD` on the files without doc comments), and
`sock3T_kernel_nodoc`, `sock3P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `sock3T` is the table of `KC.sock3.out`. -/
theorem KC.sock3.tableEq : table true KC.sock3.out = sock3T := by decide +kernel

/-- **`sock3T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem sock3T_kernel_nodoc : kTable true false [KF.v3.sock.types.src, KF.v3.sock.ip_name_lookup.src, KF.v3.clocks.monotonic_clock.src, KF.v3.clocks.system_clock.src, KF.v3.clocks.timezone.src, KF.v3.clocks.types.src] = some sock3T :=
  (kTable_of KC.sock3.importKD).trans (congrArg some KC.sock3.tableEq)

/-- `sock3P` is the resolved package of `KC.sock3.out`. -/
theorem KC.sock3.rpkgEq : (rtable true KC.sock3.out, envOf KC.sock3.out KC.sock3.deps) = sock3P := by decide +kernel

/-- **`sock3P` is kernel-checked** (without doc comments): table and type environment. -/
theorem sock3P_kernel_nodoc : kRPkg true false [KF.v3.sock.types.src, KF.v3.sock.ip_name_lookup.src, KF.v3.clocks.monotonic_clock.src, KF.v3.clocks.system_clock.src, KF.v3.clocks.timezone.src, KF.v3.clocks.types.src] = some sock3P :=
  (kRPkg_of KC.sock3.importKD).trans (congrArg some KC.sock3.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
