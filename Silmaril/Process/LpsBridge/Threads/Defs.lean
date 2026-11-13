module

public import Silmaril.Process.LpsBridge.Defs

/-!
# The single-threaded profile of the LPS bridge

LPS has one task: `clone` (x86-64 number 56) and `clone3` (435) are
*pending* arms of the native table (`NativeX86.reviewedArm` holds every arm whose ABI is not
reviewed as `pendingArm`, whose spec is `Sys.unmodeled`), and so is `futex` (202). A request
with one of these numbers is therefore `unmodeled`, an error step, whatever its flag word.
`PSafe` excludes every error step, so a process-safe execution never reaches such a request:
the single-threaded profile is a theorem (`no_thread_of_psafe` in `Threads/Thms.lean`), not a
build flag.

* `threadNo n`: `n` is the native number of `clone`, `clone3` or `futex`.
* `PendingThreadCreate segs c`: the configuration `c` is alive and has a pending syscall whose
  number is one of these.

Fork-like `clone(SIGCHLD, 0)` is also excluded: in the native table even it is pending (only
the riscv64 reference arm models it). This is stronger than the plan's statement shape, which
excluded only non-`SIGCHLD` flag words.
-/

@[expose] public section

namespace Silmaril.Process.LpsBridge

open Silmaril.Process.LPS

/-- The native x86-64 numbers of `clone` (56), `clone3` (435) and `futex` (202). -/
def threadNo (n : Nat) : Prop := n = 56 ∨ n = 435 ∨ n = 202

/-- An alive configuration with a pending `clone`, `clone3` or `futex` request. -/
def PendingThreadCreate {oracle : Oracle} (c : Config (machine oracle)) : Prop :=
  c.model.halted = none ∧ ∃ x8, (machine oracle).svcPending c.ms = some x8 ∧ threadNo x8.toNat

end Silmaril.Process.LpsBridge
