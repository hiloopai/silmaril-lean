module

public import Silmaril.Wasi.Versions.WitImport.KCert.Io29.Elab.Thms
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
# Kernel-checked imports of `wasi:io@0.2.9`

The environment, worlds and package of `KC.io29` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.io29.importKD` (the kernel importer `importKD` on the files without doc comments), and
`io29P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `io29P` is the resolved package of `KC.io29.out`. -/
theorem KC.io29.rpkgEq : (rtable false KC.io29.out, envOf KC.io29.out KC.io29.deps) = io29P := by decide +kernel

/-- **`io29P` is kernel-checked** (without doc comments): table and type environment. -/
theorem io29P_kernel_nodoc : kRPkg false false [KF.v29.io.error.src, KF.v29.io.poll.src, KF.v29.io.streams.src] = some io29P :=
  (kRPkg_of KC.io29.importKD).trans (congrArg some KC.io29.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
