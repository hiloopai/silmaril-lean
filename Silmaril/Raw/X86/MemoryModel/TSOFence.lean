-- Word-granular memory models from an earlier Silmaril development; namespaces
-- `Silmaril.Memory{,.SC,.TSO}` kept. Re-exported by `Silmaril.X86.MemoryModel.Tso`.
module

public import Silmaril.Raw.X86.MemoryModel.TSO

/-! # TSO fences drain the issuing thread's buffer -/

@[expose] public section

namespace Silmaril.Memory.TSO

universe u

variable {Tid Addr Val : Type u} [DecidableEq Tid] [DecidableEq Addr]

theorem Flush.empty_preserved {s s' : State Tid Addr Val} (h : Flush s s')
    {t : Tid} (empty : s.buffer t = []) : s'.buffer t = [] := by
  cases h with
  | head other a v rest oldest =>
      by_cases ht : t = other
      · subst other
        rw [empty] at oldest
        cases oldest
      · simpa only [Function.update_of_ne ht] using empty

theorem flushes_empty_preserved {s s' : State Tid Addr Val} (h : Flushes s s')
    {t : Tid} (empty : s.buffer t = []) : s'.buffer t = [] := by
  induction h with
  | refl => exact empty
  | tail _ last ih => exact last.empty_preserved ih

/-- Finite propagation after a fence cannot undo its draining guarantee. -/
theorem weak_fence_empty {s s' : State Tid Addr Val} {t : Tid} (h : WeakStep s (.fence t) s') :
    s'.buffer t = [] := by
  rcases h with ⟨before, after, _, hf, rest⟩
  rcases (fence_iff before after t).mp hf with ⟨empty, rfl⟩
  exact flushes_empty_preserved rest empty

end Silmaril.Memory.TSO
