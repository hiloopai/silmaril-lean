module

public import Silmaril.Process.LpsBridge.Threads.Defs
import Silmaril.Proofs.Process.LpsBridge.Threads

/-!
# The single-threaded profile of the LPS bridge: theorems

PROVED, standard axioms (proofs in `Silmaril.Proofs.Process.LpsBridge.Threads`).

* `threadNo_unmodeled`: `unmodeled` is an outcome of the native table for `clone` (56),
  `clone3` (435) and `futex` (202). That is all the proof needs; that it is the only outcome
  (true of a pending arm) is not stated.
* **`no_thread_of_psafe`**: a process-safe configuration never reaches an alive configuration
  with a pending `clone`/`clone3`/`futex` request. Every `ProcessSafe` theorem of the bridge
  therefore implies that the program creates no thread and never waits on a futex.

Assumed (model, not proved): silmaril's LPS port, in which these arms are pending.
-/

@[expose] public section

namespace Silmaril.Process.LpsBridge

open Silmaril.Process.LPS

theorem threadNo_unmodeled (i : SyscallInput) (m : Model) (h : threadNo i.sysno.toNat) :
    spec i m .unmodeled :=
  Silmaril.Proofs.Process.LpsBridge.Threads.threadNo_unmodeled i m h

/-- **A process-safe execution creates no thread.** -/
theorem no_thread_of_psafe {oracle : Oracle} {segs : List Segment} {refused : RefusalFilter}
    {Allowed : List Event → Prop} {c : Config (machine oracle)}
    (h : PSafe segs refused Allowed c) :
    ∀ tr c', Star segs spec refused c tr c' → ¬ PendingThreadCreate c' :=
  Silmaril.Proofs.Process.LpsBridge.Threads.no_thread_of_psafe h

end Silmaril.Process.LpsBridge
