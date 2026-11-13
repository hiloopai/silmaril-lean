module

public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.InstRun

@[expose] public section

/-!
# Silent deterministic runs of the copied component machine

An interface to the run tools of the reference proofs, for analyses of concrete components
outside the `Simple` fragment (`Silmaril.Wasm.Resource.CompToy`):

* `UniqueStep`, `DetRun`, `DetRunL` (deterministic runs through unlocked configurations) with
  the inversion `DetRunL.inv` and `DetRun.diverges`;
* `SRuns` (big-step silent runs of store reads, lockdown-preserving updates and observations),
  `SRuns.Quiet`, `SRuns.emit_step`, `SRuns.detRunL`;
* for `core3P P`: `hostRun_inv` (the instantiation host event), `steps_ctl_nil`, `detRunL_end`
  (a quiet deterministic run ending with the host in control is the only run without host
  events to a configuration with the host in control or locked down).

Proofs in `Silmaril.Proofs.Wasm.Component.Reference.{MachineDet,DetRun,InstSilent,InstRun}`.
-/
