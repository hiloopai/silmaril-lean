module

public import Silmaril.Wasi.Versions.WitImport.KCert.Rand3.Elab.Thms
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
# Kernel-checked imports of `wasi:random@0.3.2`

The environment, worlds and package of `KC.rand3` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.rand3.importKD` (the kernel importer `importKD` on the files without doc comments), and
`rand3T_kernel_nodoc`, `rand3P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `rand3T` is the table of `KC.rand3.out`. -/
theorem KC.rand3.tableEq : table true KC.rand3.out = rand3T := by decide +kernel

/-- **`rand3T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem rand3T_kernel_nodoc : kTable true false [KF.v3.rand.insecure_seed.src, KF.v3.rand.insecure.src, KF.v3.rand.random.src] = some rand3T :=
  (kTable_of KC.rand3.importKD).trans (congrArg some KC.rand3.tableEq)

/-- `rand3P` is the resolved package of `KC.rand3.out`. -/
theorem KC.rand3.rpkgEq : (rtable true KC.rand3.out, envOf KC.rand3.out KC.rand3.deps) = rand3P := by decide +kernel

/-- **`rand3P` is kernel-checked** (without doc comments): table and type environment. -/
theorem rand3P_kernel_nodoc : kRPkg true false [KF.v3.rand.insecure_seed.src, KF.v3.rand.insecure.src, KF.v3.rand.random.src] = some rand3P :=
  (kRPkg_of KC.rand3.importKD).trans (congrArg some KC.rand3.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
