module

public import Silmaril.Process.LpsBridge.Threads.Defs

/-!
# Proofs: no thread is created by a process-safe execution

* `clone_unmodeled`, `clone3_unmodeled`, `futex_unmodeled`: `unmodeled` is an outcome of the
  native table for these numbers (pending arms).
* `no_thread_of_psafe`: from a process-safe configuration, no reachable configuration has a
  pending `clone`/`clone3`/`futex` request, because that request would be an error step.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.LpsBridge.Threads

open Silmaril.Process.LPS
open Silmaril.Process.LpsBridge

theorem clone_unmodeled (i : SyscallInput) (m : Model) (h : i.sysno.toNat = 56) :
    spec i m .unmodeled := by
  simp only [spec, NativeX86.extendedSyscallSpec, dispatch, h]
  rfl

theorem clone3_unmodeled (i : SyscallInput) (m : Model) (h : i.sysno.toNat = 435) :
    spec i m .unmodeled := by
  simp only [spec, NativeX86.extendedSyscallSpec, dispatch, h]
  rfl

theorem futex_unmodeled (i : SyscallInput) (m : Model) (h : i.sysno.toNat = 202) :
    spec i m .unmodeled := by
  simp only [spec, NativeX86.extendedSyscallSpec, dispatch, h]
  rfl

theorem threadNo_unmodeled (i : SyscallInput) (m : Model) (h : threadNo i.sysno.toNat) :
    spec i m .unmodeled := by
  rcases h with h | h | h
  · exact clone_unmodeled i m h
  · exact clone3_unmodeled i m h
  · exact futex_unmodeled i m h

theorem no_thread_of_psafe {oracle : Oracle} {segs : List Segment} {refused : RefusalFilter}
    {Allowed : List Event → Prop} {c : Config (machine oracle)}
    (h : PSafe segs refused Allowed c) :
    ∀ tr c', Star segs spec refused c tr c' → ¬ PendingThreadCreate c' := by
  rintro tr ⟨ms, model⟩ hs ⟨alive, x8, hp, hn⟩
  exact h.2 tr _ [] hs (.syscallUnmodeled alive hp (threadNo_unmodeled _ _ hn))

end Silmaril.Proofs.Process.LpsBridge.Threads
