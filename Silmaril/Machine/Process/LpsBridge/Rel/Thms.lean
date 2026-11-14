module

public import Silmaril.Machine.Process.LpsBridge.Rel.Defs
public import Silmaril.Proofs.Machine.Process.LpsBridge.Rel

/-! # The LPS bridge over relational machines: theorems (header)

PROVED (standard axioms; proofs in
`Silmaril.Proofs.Machine.Process.LpsBridge.Rel`, namespace
`Silmaril.Proofs.Machine.Process.LpsBridge`). Every statement is generic in the native step
`nstep`, the deterministic machine `c` with `Agrees nstep c`, the relational machine `A` with
`Le (ofFun c) A`, the segments, the oracle and the refusal filter.

* `sstepF_step`, `sstepF_trap`: from an aligned configuration of `flagMachine oracle nstep`,
  an agreeing step (resp. the trap) is the only LPS step.
* `psafeF_of_safeN`, and **`psafe_of_safeNR`**: `∀ n, SafeNR A Q n m` gives process safety
  (`PSafeF`), given process safety at aligned `Q` states with the same model.
* `psafeF_syscall`, `psafeF_exit`: the syscall half and the `exit` arm over `flagMachine`.
* `mustExitF_exit`, `mustExitF_of_mustFun`, and **`mustExit_of_must`**:
  `Must A ⊤ (ExitReq ∧ rdi &&& 255 = code) m` gives `MustExitInAt … [code]` (every execution
  exits with `code`, never errors, never stalls).
* `initF_aligned`, `processSafeF_of_launchR`, `mustExitF_of_launchR`: the launch forms.
* The Ext8 instance: `flagMachine_eight` (`flagMachine oracle x86NativeStep8 = machine
  oracle`, by `rfl`), **`agrees_open8 : Agrees x86NativeStep8 Open.step`** (from
  `open_step_trap`/`native8_open`, the facts behind `sstep_open`), `alignedF_iff`,
  `psafeF_iff`: so the old bridge is the instance `A := ofFun Open.step` (or anything above
  it, such as `loosen Open.isa ⊤`).

Caveat: `psafe_of_safeNR` and `mustExit_of_must` read the run out of `c`, not out of `A`.
`A` may have no outcome at some state (then `SafeNR A`/`Must A` hold vacuously there); this
is harmless here because the hypothesis `Le (ofFun c) A` transfers the property *down* to
`ofFun c`, which always has an outcome.

Not here: the `read`/`write` arms over `flagMachine` (they are stated for `machine oracle` in
`LpsBridge`; `Z4` owns their generalisation), lazy reservations.
-/
