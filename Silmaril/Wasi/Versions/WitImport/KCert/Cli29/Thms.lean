module

public import Silmaril.Wasi.Versions.WitImport.KCert.Cli29.Elab.Thms
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
# Kernel-checked imports of `wasi:cli@0.2.9`

The environment, worlds and package of `KC.cli29` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.cli29.importKD` (the kernel importer `importKD` on the files without doc comments), and
`cli29P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `cli29P` is the resolved package of `KC.cli29.out`. -/
theorem KC.cli29.rpkgEq : (rtable false KC.cli29.out, envOf KC.cli29.out KC.cli29.deps) = cli29P := by decide +kernel

/-- **`cli29P` is kernel-checked** (without doc comments): table and type environment. -/
theorem cli29P_kernel_nodoc : kRPkg false false [KF.v29.cli.environment.src, KF.v29.cli.exit.src, KF.v29.cli.run.src, KF.v29.cli.stdio.src, KF.v29.cli.terminal.src, KF.v29.io.error.src, KF.v29.io.poll.src, KF.v29.io.streams.src] = some cli29P :=
  (kRPkg_of KC.cli29.importKD).trans (congrArg some KC.cli29.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
