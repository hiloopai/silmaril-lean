module

public import Silmaril.X86.Open.Thms
public import Silmaril.Process.LpsBridge.Defs
public import Silmaril.Proofs.Process.LpsBridge.Instr
public import Silmaril.Proofs.Process.LpsBridge.Syscall
public import Silmaril.Proofs.Process.LpsBridge.Launch
public import Silmaril.Proofs.Process.LpsBridge.Write
public import Silmaril.Proofs.Process.LpsBridge.Read
public import Silmaril.Proofs.Process.LpsBridge.MustExit

/-! # The open-machine/LPS bridge: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Process.LpsBridge.*`, namespace
`Silmaril.Proofs.Process.LpsBridge`). Every statement is program-independent: it holds
for every segment list, flag oracle, refusal filter and launch.

**Instruction half** (`Instr`):
* `open_step_trap`: the open machine is stuck at `0F 05`.
* `account_open`, `sstep_open`: a non-`syscall` open step from an aligned configuration is
  the only LPS step, with the same model and oracle counter.
* `account_trap`, `sstep_trap`: at `0F 05` the only LPS step records the pending number.
* **`psafe_of_safeN`**: `∀ n, SafeN Open.isa Q n m` (the safety notion of the `FnSpec` link
  logic; since round 4 the generic `Silmaril.X86.Safe.SafeN`, so this bridge no longer
  imports the linker) for the state of an aligned configuration gives process safety, given
  process safety at every aligned `Q` state with the same model. **Ext8 only**: the LPS
  process machine executes `X86.Ext`/`Ext8` forms; a body that uses an `Ext9` form or a jump
  table has an `Open9` `SafeN` (e.g. `len1_composed9`), which this bridge does not consume.

**Syscall half** (`Syscall`):
* `halted_no_step`, `star_halted`.
* **`psafe_syscall`**: an aligned configuration at `0F 05` is process-safe if the request is
  modelled and every outcome of the native table satisfies `Outcomes` (unkilled; a resumed
  outcome continues process-safe from `resume`; a halting outcome's trace is allowed).
* `exit_dispatch` (copied from silmaril-lean `Sha256Cli.exit_dispatch`), **`psafe_exit`**:
  the `exit`/`exit_group` arm.

**Launch** (`Launch`):
* `init_aligned`: `X86Launch.init` is aligned with `launchState`.
* **`processSafe_of_launch`**: the whole-process schema.

**The `write` arm** (`Write`, round 3):
* `write_dispatch`, `write_channel_iff` (adapted from silmaril-lean `Sha256Cli.WriteSpec`/
  `WriteStep` to any live channel), **`writeArm_holds : Task.writeArm`** (with the corrected
  statement: copy-in recorded, `ch ≠ 0`, modelled range), **`psafe_write`**: an aligned
  configuration at `0F 05` with `rax = 1` on a live channel is process-safe if every resumed
  configuration after a non-empty partial write `ds` is process-safe for the traces after
  `ds.map (writeEv ch)`.

**Total correctness** (`MustExit`, round 3):
* `mustExit_exit`, **`mustExit_of_run`**: a terminating open run (`run Open.step k m = some m'`)
  from an aligned configuration to an `exit` request gives LPS's must-exit tier
  `MustExitInAt [rdi &&& 255]` (every execution exits with that status, never errors, never
  stalls); `mustExit_of_launch`, the whole-process form.

**The `read` arm** (`Read`):
* `read_dispatch`, `read_stdin_iff`, **`readArm_holds : Task.readArm`** (with the corrected
  statement: stdin only, `access_ok` and a writable range assumed; outcomes `ret = 0` at count
  `0` or EOF, otherwise a non-empty prefix of stdin delivered at `buf`, stdin advanced, one
  `readEv 0` per byte; never `unmodeled`). Helpers: `readBytesAux_isSome_of_le`,
  `takeFrom_length_le`, `lenWord_toNat`, `modify_emit_pure_iff`, `retOnly_iff`.
  Non-vacuity and mutation on a concrete one-byte stdin read: `readNv_hyps`, `readNv_pos`,
  `readNv_wrongByte`, `readNv_notZero`.
* The process-level `read` arm (resume obligations) is stated over `flagMachine` in
  `Silmaril.Process.IoSpec` (`readArm`, `armSound_read`, `sound_lpsEnv`).

No open Tasks remain in this topic. Not attempted: a must-exit bridge through `read`/`write`
(only exit-only tails are covered), `read` from descriptors other than stdin, other
syscalls, lazy (`MAP_NORESERVE`) reservations.

Assumed (models, not proved): silmaril's LPS port and the `X86.Ext`/`Ext8` semantics.
-/
