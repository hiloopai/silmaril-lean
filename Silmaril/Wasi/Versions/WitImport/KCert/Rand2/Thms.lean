module

public import Silmaril.Wasi.Versions.WitImport.KCert.Rand2.Elab.Thms
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
# Kernel-checked imports of `wasi:random@0.2.12`

The environment, worlds and package of `KC.rand2` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.rand2.importKD` (the kernel importer `importKD` on the files without doc comments), and
`rand2T_kernel_nodoc`, `rand2P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `rand2T` is the table of `KC.rand2.out`. -/
theorem KC.rand2.tableEq : table false KC.rand2.out = rand2T := by decide +kernel

/-- **`rand2T` is kernel-checked** (without doc comments): the importer, evaluated in the kernel
in steps, gives it. -/
theorem rand2T_kernel_nodoc : kTable false false [KF.v2.rand.insecure_seed.src, KF.v2.rand.insecure.src, KF.v2.rand.random.src] = some rand2T :=
  (kTable_of KC.rand2.importKD).trans (congrArg some KC.rand2.tableEq)

/-- `rand2P` is the resolved package of `KC.rand2.out`. -/
theorem KC.rand2.rpkgEq : (rtable false KC.rand2.out, envOf KC.rand2.out KC.rand2.deps) = rand2P := by decide +kernel

/-- **`rand2P` is kernel-checked** (without doc comments): table and type environment. -/
theorem rand2P_kernel_nodoc : kRPkg false false [KF.v2.rand.insecure_seed.src, KF.v2.rand.insecure.src, KF.v2.rand.random.src] = some rand2P :=
  (kRPkg_of KC.rand2.importKD).trans (congrArg some KC.rand2.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
