module

public import Silmaril.Wasi.Versions.WitImport.KCert.Cli3.Elab.Thms
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
# Kernel-checked imports of `wasi:cli@0.3.2`

The environment, worlds and package of `KC.cli3` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.cli3.importKD` (the kernel importer `importKD` on the files without doc comments), and
`cli3T_kernel_nodoc`, `cli3P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `cli3T` is the table of `KC.cli3.out`. -/
theorem KC.cli3.tableEq : table true KC.cli3.out = cli3T := by decide +kernel

/-- **`cli3T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem cli3T_kernel_nodoc : kTable true false [KF.v3.cli.environment.src, KF.v3.cli.exit.src, KF.v3.cli.run.src, KF.v3.cli.stdio.src, KF.v3.cli.terminal.src] = some cli3T :=
  (kTable_of KC.cli3.importKD).trans (congrArg some KC.cli3.tableEq)

/-- `cli3P` is the resolved package of `KC.cli3.out`. -/
theorem KC.cli3.rpkgEq : (rtable true KC.cli3.out, envOf KC.cli3.out KC.cli3.deps) = cli3P := by decide +kernel

/-- **`cli3P` is kernel-checked** (without doc comments): table and type environment. -/
theorem cli3P_kernel_nodoc : kRPkg true false [KF.v3.cli.environment.src, KF.v3.cli.exit.src, KF.v3.cli.run.src, KF.v3.cli.stdio.src, KF.v3.cli.terminal.src] = some cli3P :=
  (kRPkg_of KC.cli3.importKD).trans (congrArg some KC.cli3.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
