module

public import Silmaril.Wasi.Versions.WitImport.KCert.Rand29.Elab.Thms
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
# Kernel-checked imports of `wasi:random@0.2.9`

The environment, worlds and package of `KC.rand29` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.rand29.importKD` (the kernel importer `importKD` on the files without doc comments), and
`rand29P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `rand29P` is the resolved package of `KC.rand29.out`. -/
theorem KC.rand29.rpkgEq : (rtable false KC.rand29.out, envOf KC.rand29.out KC.rand29.deps) = rand29P := by decide +kernel

/-- **`rand29P` is kernel-checked** (without doc comments): table and type environment. -/
theorem rand29P_kernel_nodoc : kRPkg false false [KF.v29.rand.insecure_seed.src, KF.v29.rand.insecure.src, KF.v29.rand.random.src] = some rand29P :=
  (kRPkg_of KC.rand29.importKD).trans (congrArg some KC.rand29.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
