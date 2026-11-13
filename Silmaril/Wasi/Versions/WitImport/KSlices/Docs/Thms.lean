module

public import Silmaril.Wasi.Versions.WitImport.KCert.Docs.V2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Docs.V3.Thms
public import Silmaril.Wasi.Versions.WitImport.RSlices.Defs

@[expose] public section

/-!
# The packages of the switched checks, kernel-checked with doc comments parsed

`p2P_kernel` and `p3P_kernel`: `p2P` and `p3P` (`WitImport.RSlices`), which the switched checks
`P2.cliOk` and `P3.ok3` read their signatures and kinds from, are what the kernel importer
computes from the vendored 0.2.12 and 0.3.2 `cli`, `clocks` and `filesystem` files with their doc
comments, every token parsed (`kRPkg`, the `<P>_kernel` theorems of `KCert/Docs/*`). Unlike
`p2P_kernel_tokens` and `p3P_kernel_tokens` (`Silmaril.Wasi.Versions.WitImport.KSlices`), no
assumption about doc-comment tokens remains: `Silmaril.Wasi.Versions.WitImport.KErase` proves that
they cannot change a resolved package. What stays trusted is the text glue of `wit_src%`
(`withHeader`, `demoteParamDocs`), which runs in the evaluator.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-- **`p2P`** from the kernel importer on the vendored 0.2.12 files, doc comments parsed. -/
theorem p2P_kernel :
    (do
      let c ← kRPkg false false
        [KF.v2.cli.environment.full, KF.v2.cli.exit.full, KF.v2.cli.run.full,
          KF.v2.cli.stdio.full, KF.v2.cli.terminal.full, KF.v2.io.error.full,
          KF.v2.io.poll.full, KF.v2.io.streams.full]
      let k ← kRPkg false false
        [KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full,
          KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full,
          KF.v2.io.streams.full]
      let f ← kRPkg false false
        [KF.v2.fs.types.full, KF.v2.fs.preopens.full, KF.v2.clocks.monotonic_clock.full,
          KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full,
          KF.v2.io.poll.full, KF.v2.io.streams.full]
      pure (rappend c (rappend k f))) = some p2P := by
  rw [cli2P_kernel, clocks2P_kernel, fs2P_kernel]
  rfl

/-- **`p3P`** from the kernel importer on the vendored 0.3.2 files, doc comments parsed. -/
theorem p3P_kernel :
    (do
      let c ← kRPkg true false
        [KF.v3.cli.environment.full, KF.v3.cli.exit.full, KF.v3.cli.run.full,
          KF.v3.cli.stdio.full, KF.v3.cli.terminal.full]
      let k ← kRPkg true false
        [KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full,
          KF.v3.clocks.timezone.full, KF.v3.clocks.types.full]
      let f ← kRPkg true false
        [KF.v3.fs.types.full, KF.v3.fs.preopens.full, KF.v3.clocks.monotonic_clock.full,
          KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full]
      pure (rappend c (rappend k f))) = some p3P := by
  rw [cli3P_kernel, clocks3P_kernel, fs3P_kernel]
  rfl

end Silmaril.Wasi.Versions.WitImport
