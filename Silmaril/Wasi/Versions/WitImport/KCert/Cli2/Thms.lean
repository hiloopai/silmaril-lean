module

public import Silmaril.Wasi.Versions.WitImport.KCert.Cli2.Elab.Thms
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
# Kernel-checked imports of `wasi:cli@0.2.12`

The environment, worlds and package of `KC.cli2` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.cli2.importKD` (the kernel importer `importKD` on the files without doc comments), and
`cli2T_kernel_nodoc`, `cli2P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `cli2T` is the table of `KC.cli2.out`. -/
theorem KC.cli2.tableEq : table false KC.cli2.out = cli2T := by decide +kernel

/-- **`cli2T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem cli2T_kernel_nodoc : kTable false false [KF.v2.cli.environment.src, KF.v2.cli.exit.src, KF.v2.cli.run.src, KF.v2.cli.stdio.src, KF.v2.cli.terminal.src, KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some cli2T :=
  (kTable_of KC.cli2.importKD).trans (congrArg some KC.cli2.tableEq)

/-- `cli2P` is the resolved package of `KC.cli2.out`. -/
theorem KC.cli2.rpkgEq : (rtable false KC.cli2.out, envOf KC.cli2.out KC.cli2.deps) = cli2P := by decide +kernel

/-- **`cli2P` is kernel-checked** (without doc comments): table and type environment. -/
theorem cli2P_kernel_nodoc : kRPkg false false [KF.v2.cli.environment.src, KF.v2.cli.exit.src, KF.v2.cli.run.src, KF.v2.cli.stdio.src, KF.v2.cli.terminal.src, KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some cli2P :=
  (kRPkg_of KC.cli2.importKD).trans (congrArg some KC.cli2.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
