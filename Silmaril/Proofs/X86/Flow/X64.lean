module

public import Silmaril.X86.Flow.X64.Defs

/-! Proofs for `Silmaril.X86.Flow.X64`: the decoder reads a prefix (`stable`). -/

@[expose] public section

namespace Silmaril.Proofs.X86.Flow.X64

open Silmaril.X86 (Byte)
open Silmaril.X86.Flow (FlowDec)
open Silmaril.X86.Flow.X64

theorem scan_ge (w : List Byte) : ∀ k l r, scan w k l = some r → l ≤ r.2 ∧ r.2 ≤ w.length
  | 0, _, _, h => by simp [scan] at h
  | k + 1, l, r, h => by
    unfold scan at h
    by_cases hl : l ≤ w.length
    · simp only [hl, ↓reduceIte] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨Nat.le_refl _, hl⟩
      · have := scan_ge w k (l + 1) r h; omega
    · simp [hl] at h

theorem scan_take (w : List Byte) (m : Nat) (x : List Byte) :
    ∀ k l r, scan w k l = some r → r.2 = m → m ≤ w.length → scan (w.take m ++ x) k l = some r
  | 0, _, _, h, _, _ => by simp [scan] at h
  | k + 1, l, r, h, hm, hw => by
    have hge := scan_ge w (k + 1) l r h
    unfold scan at h ⊢
    by_cases hl : l ≤ w.length
    · have hl' : l ≤ (w.take m ++ x).length := by simp; omega
      have ht : (w.take m ++ x).take l = w.take l := by
        rw [List.take_append_of_le_length (by simp; omega)]
        rw [List.take_take]; congr 1; omega
      simp only [hl, ↓reduceIte] at h
      simp only [hl', ↓reduceIte, ht]
      split at h
      · exact h
      · exact scan_take w m x k (l + 1) r h hm hw
    · simp [hl] at h

/-- **The decoder reads a prefix.** -/
theorem stable : dec.Stable := by
  intro w i l h
  have hle := (scan_ge w 15 1 (i, l) h).2
  exact ⟨hle, fun x => scan_take w l x 15 1 (i, l) h rfl hle⟩

end Silmaril.Proofs.X86.Flow.X64
