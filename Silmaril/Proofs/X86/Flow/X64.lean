module

public import Silmaril.X86.Flow.X64.Defs

/-! Proofs for `Silmaril.X86.Flow.X64`: the decoder reads a prefix (`stable`). -/

@[expose] public section

namespace Silmaril.Proofs.X86.Flow.X64

open Silmaril.X86 (Byte)
open Silmaril.X86.Flow (FlowDec)
open Silmaril.X86.Flow.X64

theorem scan_append (w x : List Byte) :
    ∀ k l r, scan w k l = some r → scan (w ++ x) k l = some r ∧ r.2 ≤ w.length
  | 0, _, _, h => by simp [scan] at h
  | k + 1, l, r, h => by
    unfold scan at h ⊢
    by_cases hl : l ≤ w.length
    · have hl' : l ≤ (w ++ x).length := by simp; omega
      have ht : (w ++ x).take l = w.take l := List.take_append_of_le_length hl
      simp only [hl, ↓reduceIte] at h
      simp only [hl', ↓reduceIte, ht]
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, hl⟩
      · exact scan_append w x k (l + 1) r h
    · simp [hl] at h

/-- **The decoder reads a prefix.** -/
theorem stable : dec.Stable := by
  intro w x i l h _
  exact (scan_append w x 15 1 (i, l) h).1

/-- The length is at most the slice's. -/
theorem decode_le {w : List Byte} {i : Info} {l : Nat} (h : decode w = some (i, l)) :
    l ≤ w.length :=
  (scan_append w [] 15 1 (i, l) h).2

end Silmaril.Proofs.X86.Flow.X64
