module

public import Silmaril.Machine.Process.IoSpec.Defs
public import Silmaril.Proofs.Machine.Process.IoSpec.Psafe
public import Silmaril.Proofs.Machine.Process.IoSpec.Arms
public import Silmaril.Proofs.Machine.Process.IoSpec.Rules
public import Silmaril.Proofs.Machine.Process.IoSpec.Rung12

/-! # `IoSpec`: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Machine.Process.IoSpec.*`,
namespace `Silmaril.Proofs.Machine.Process.IoSpec`). Every statement is generic in the agreeing
native step `nstep`, the deterministic machine `c`, the segments, the oracle and the refusal
filter.

**Soundness** (`Psafe`):
* `trapRequestF_eq`, `next_mono`, `ioSafeN_mono`, `Good`, `aligned_cases`, `good_nil`,
  `good_noerr`, `good_step`, `good_star`.
* **`ioSafe_psafe`**: `Agrees nstep c`, `Sound E segs refused`, an aligned configuration
  whose open state is `IoSafeN c E Q n m e A` for every `n` (with `E.Abs e` of its model),
  and process safety at the `Q` exits give `PSafeF segs refused A`.

**The arms** (`Arms`):
* **`sound_ofArms`**: a list of sound arms is a sound environment.
* **`armSound_exit`**, **`armSound_write`**, **`armSound_read`**, **`sound_lpsEnv`**.

**Proof rules** (`Rules`):
* `ioSafe_of_q`; **`ioSafe_of_safeN`** (syscall-free `SafeN` code lifts, no event, model
  unchanged); **`ioSafe_trap`**; **`ioSafe_exit`** (on `lpsEnv`); `ioSafe_psafeLps`.

**Regression: rung 12 through `IoSpec`** (`Rung12`):
* `rung12_ioSafe` (any `c` extending `Open.step`), **`rung12_processSafe_io`**
  (`x86WithFlagOracle8`), **`rung12_processSafe9_io`** (`x86WithFlagOracle9`),
  **`rung12_processSafeStr`** (`x86WithFlagOracle9Str`, Z4's string machine),
  **`rung12_complete_io`** (the statement of `rung12_complete`; must-exit half still from
  `rung12_mustExit`), `rung12_nonvacuousStr`.

Not here: `IoFnSpec` (an `FnSpec` with environment pre/post), its call rule (`io_call_rule`)
and the total variant `IoSafeT` (zlib-binary.md §5.1); `read` from descriptors other than
stdin; other syscalls (`brk` is M12's `LpsBrk`, `arch_prctl`/`set_tid_address` are not
wrapped yet); lazy reservations.

Assumed (models, not proved): silmaril's LPS port and the handwritten x86 semantics behind
the native steps.
-/
