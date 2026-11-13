module

public import Silmaril.Wasi.Versions.WitImport.KCert.Http29.Elab.Thms
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
# Kernel-checked imports of `wasi:http@0.2.9`

The environment, worlds and package of `KC.http29` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.http29.importKD` (the kernel importer `importKD` on the files without doc comments), and
`http29P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `http29P` is the resolved package of `KC.http29.out`. -/
theorem KC.http29.rpkgEq : (rtable false KC.http29.out, envOf KC.http29.out KC.http29.deps) = http29P := by decide +kernel

/-- **`http29P` is kernel-checked** (without doc comments): table and type environment. -/
theorem http29P_kernel_nodoc : kRPkg false false [KF.v29.http.types.src, KF.v29.http.handler.src, KF.v29.clocks.monotonic_clock.src, KF.v29.clocks.wall_clock.src, KF.v29.clocks.timezone.src, KF.v29.io.error.src, KF.v29.io.poll.src, KF.v29.io.streams.src] = some http29P :=
  (kRPkg_of KC.http29.importKD).trans (congrArg some KC.http29.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
