module

public import Silmaril.Wasi.Versions.WitImport.KCert.Tokens.V2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Tokens.V3.Thms
public import Silmaril.Wasi.Versions.WitImport.RSlices.Defs

@[expose] public section

/-!
# The packages of the switched checks, kernel-checked

`P2.cliOk` and `P3.ok3` (track `wf-p2-switch`) read their signatures and kinds from `p2P` and
`p3P` (`WitImport.RSlices`), which append resolved packages that `wit_rpkg%` computes outside
the kernel. Track `wf-p2-kernel` checks each of those packages in the kernel on the vendored
files' tokens (`<P>_kernel_tokens`). Here the two are put together: `p2P` and `p3P` are what
the kernel importer computes from the vendored 0.2.12 and 0.3.2 `cli`, `clocks` and
`filesystem` files, so the kinds the switched checks use are no longer entered by hand or taken
from an unchecked evaluation.

These theorems drop the doc-comment tokens after lexing (`kRPkgTok`, `KTokens`). The same
equations with every token parsed are `p2P_kernel` and `p3P_kernel`
(`Silmaril.Wasi.Versions.WitImport.KSlices.Docs`), from the proof that doc comments cannot change a
resolved package (`Silmaril.Wasi.Versions.WitImport.KErase`). What stays trusted is the text glue
`withHeader`/`demoteParamDocs` inside `wit_src%`.

A Silmaril addition (integration an earlier step of the WASI full workflow).
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-- **`p2P`** from the kernel importer on the vendored 0.2.12 files' tokens. -/
theorem p2P_kernel_tokens :
    (do
      let c ← kRPkgTok false false
        [KF.v2.cli.environment.full, KF.v2.cli.exit.full, KF.v2.cli.run.full,
          KF.v2.cli.stdio.full, KF.v2.cli.terminal.full, KF.v2.io.error.full,
          KF.v2.io.poll.full, KF.v2.io.streams.full]
      let k ← kRPkgTok false false
        [KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full,
          KF.v2.clocks.timezone.full, KF.v2.io.error.full, KF.v2.io.poll.full,
          KF.v2.io.streams.full]
      let f ← kRPkgTok false false
        [KF.v2.fs.types.full, KF.v2.fs.preopens.full, KF.v2.clocks.monotonic_clock.full,
          KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full,
          KF.v2.io.poll.full, KF.v2.io.streams.full]
      pure (rappend c (rappend k f))) = some p2P := by
  rw [cli2P_kernel_tokens, clocks2P_kernel_tokens, fs2P_kernel_tokens]
  rfl

/-- **`p3P`** from the kernel importer on the vendored 0.3.2 files' tokens. -/
theorem p3P_kernel_tokens :
    (do
      let c ← kRPkgTok true false
        [KF.v3.cli.environment.full, KF.v3.cli.exit.full, KF.v3.cli.run.full,
          KF.v3.cli.stdio.full, KF.v3.cli.terminal.full]
      let k ← kRPkgTok true false
        [KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full,
          KF.v3.clocks.timezone.full, KF.v3.clocks.types.full]
      let f ← kRPkgTok true false
        [KF.v3.fs.types.full, KF.v3.fs.preopens.full, KF.v3.clocks.monotonic_clock.full,
          KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full]
      pure (rappend c (rappend k f))) = some p3P := by
  rw [cli3P_kernel_tokens, clocks3P_kernel_tokens, fs3P_kernel_tokens]
  rfl

end Silmaril.Wasi.Versions.WitImport
