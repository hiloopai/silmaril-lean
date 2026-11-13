module

public import Silmaril.Wasi.Versions.WitImport.KCert.Fs29.Elab.Thms
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
# Kernel-checked imports of `wasi:filesystem@0.2.9`

The environment, worlds and package of `KC.fs29` (`wit_kcert`, `Silmaril.Wasi.Versions.WitImport.KQuote`),
`KC.fs29.importKD` (the kernel importer `importKD` on the files without doc comments), and
`fs29P_kernel_nodoc`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- `fs29P` is the resolved package of `KC.fs29.out`. -/
theorem KC.fs29.rpkgEq : (rtable false KC.fs29.out, envOf KC.fs29.out KC.fs29.deps) = fs29P := by decide +kernel

/-- **`fs29P` is kernel-checked** (without doc comments): table and type environment. -/
theorem fs29P_kernel_nodoc : kRPkg false false [KF.v29.fs.types.src, KF.v29.fs.preopens.src, KF.v29.clocks.monotonic_clock.src, KF.v29.clocks.wall_clock.src, KF.v29.clocks.timezone.src, KF.v29.io.error.src, KF.v29.io.poll.src, KF.v29.io.streams.src] = some fs29P :=
  (kRPkg_of KC.fs29.importKD).trans (congrArg some KC.fs29.rpkgEq)


end Silmaril.Wasi.Versions.WitImport
