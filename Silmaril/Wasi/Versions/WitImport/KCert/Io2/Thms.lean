module

public import Silmaril.Wasi.Versions.WitImport.KCert.Io2.Elab.Thms
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
# Kernel-checked imports of `wasi:io@0.2.12`

The environment, worlds and package of `KC.io2` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.io2.importKD` (the kernel importer `importKD` on the files without doc comments), and
`io2T_kernel_nodoc`, `io2D_kernel_nodoc`, `io2P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `io2T` is the table of `KC.io2.out`. -/
theorem KC.io2.tableEq : table false KC.io2.out = io2T := by decide +kernel

/-- **`io2T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem io2T_kernel_nodoc : kTable false false [KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some io2T :=
  (kTable_of KC.io2.importKD).trans (congrArg some KC.io2.tableEq)

/-- `io2D` are the drops of `KC.io2.out`. -/
theorem KC.io2.dropsEq : drops false KC.io2.out = io2D := by decide +kernel

/-- **`io2D` is kernel-checked** (without doc comments). -/
theorem io2D_kernel_nodoc : kDrops false [KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some io2D :=
  (kDrops_of KC.io2.importKD).trans (congrArg some KC.io2.dropsEq)

/-- `io2P` is the resolved package of `KC.io2.out`. -/
theorem KC.io2.rpkgEq : (rtable false KC.io2.out, envOf KC.io2.out KC.io2.deps) = io2P := by decide +kernel

/-- **`io2P` is kernel-checked** (without doc comments): table and type environment. -/
theorem io2P_kernel_nodoc : kRPkg false false [KF.v2.io.error.src, KF.v2.io.poll.src, KF.v2.io.streams.src] = some io2P :=
  (kRPkg_of KC.io2.importKD).trans (congrArg some KC.io2.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
