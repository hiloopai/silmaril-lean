module

public import Silmaril.Wasm.Tools.Wast.Lex.Defs

/-!
# `blankAnnots` blanks only annotations: proofs

Proofs for `Silmaril.Wasm.Tools.Wast.Lex.Thms` (`blankAnnots_blanked`):
`blankAnnots s` has the size of `s`, and every byte it changes is turned into a space, was
not a line break, and lies in a range `[i, j)` that starts with `(@` and that the annotation
scanner `annotEnd` closes at `j`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

/-- `[i, j)` is an annotation for the byte scanner: `(@` at `i`, closed at `j`. -/
def AnnotRange (s : ByteArray) (i j : Nat) : Prop :=
  byteAt s i = 40 ∧ byteAt s (i + 1) = 64 ∧ annotEnd s i (s.size + 1) 1 (i + 2) = .ok j

/-- `out` is `s` with some bytes of annotations replaced by spaces, line breaks kept. -/
def Blanked (s out : ByteArray) : Prop :=
  out.size = s.size ∧ ∀ k, out.get! k = s.get! k ∨
    (out.get! k = 32 ∧ s.get! k ≠ 10 ∧ s.get! k ≠ 13 ∧ ∃ i j, i ≤ k ∧ k < j ∧ AnnotRange s i j)

theorem get!_eq_getElem! (o : ByteArray) (k : Nat) : o.get! k = o[k]! := by
  obtain ⟨bs⟩ := o
  by_cases hk : k < bs.size
  · rw [getElem!_pos (⟨bs⟩ : ByteArray) k hk]
    show bs[k]! = bs[k]
    rw [getElem!_pos bs k hk]
  · rw [getElem!_neg (⟨bs⟩ : ByteArray) k hk]
    show bs[k]! = default
    rw [getElem!_neg bs k hk]

theorem get!_set! (o : ByteArray) (k j : Nat) (v : UInt8) :
    (o.set! k v).get! j = if k = j ∧ k < o.size then v else o.get! j := by
  rw [get!_eq_getElem!, get!_eq_getElem!]
  by_cases hkj : k = j
  · subst hkj
    by_cases hk : k < o.size
    · simp [hk]
    · rw [getElem!_neg (o.set! k v) k (by simpa using hk), getElem!_neg o k hk]
      simp [hk]
  · rw [ByteArray.getElem!_set!_ne _ _ _ _ hkj]
    simp [hkj]

theorem blanked_refl (s : ByteArray) : Blanked s s := ⟨rfl, fun _ => .inl rfl⟩

theorem blankRange_go {s : ByteArray} :
    ∀ (n k : Nat) (o : ByteArray), Blanked s o →
      (∀ m, k ≤ m → m < k + n → ∃ i j, i ≤ m ∧ m < j ∧ AnnotRange s i j) →
      Blanked s (blankRange.go n k o)
  | 0, _, _, h, _ => h
  | n + 1, k, o, h, hr => by
    simp only [blankRange.go]
    apply blankRange_go n (k + 1)
    · split
      · rename_i hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        refine ⟨by simp [h.1], fun k' => ?_⟩
        rw [get!_set!]
        split
        · rename_i hk
          obtain ⟨rfl, -⟩ := hk
          right
          have hs : s.get! k ≠ 10 ∧ s.get! k ≠ 13 := by
            rcases h.2 k with he | ⟨-, h10, h13, -⟩
            · rw [← he]; exact hc
            · exact ⟨h10, h13⟩
          exact ⟨rfl, hs.1, hs.2, hr k (Nat.le_refl _) (by omega)⟩
        · exact h.2 k'
      · exact h
    · intro m hm hm'
      exact hr m (by omega) (by omega)

theorem blankRange_blanked {s o : ByteArray} {i j : Nat} (h : Blanked s o)
    (hr : AnnotRange s i j) : Blanked s (blankRange o i j) :=
  blankRange_go _ _ _ h fun m hm hm' => ⟨i, j, hm, by omega, hr⟩

theorem blankFrom_blanked (s : ByteArray) :
    ∀ (fuel i : Nat) (out : ByteArray), Blanked s out → Blanked s (blankFrom s fuel i out)
  | 0, _, _, h => h
  | fuel + 1, i, out, h => by
    simp only [blankFrom]
    split
    · exact h
    · split
      · exact blankFrom_blanked s fuel _ _ h
      · split
        · split
          · exact blankFrom_blanked s fuel _ _ h
          · exact h
        · split
          · rename_i hat
            split
            · rename_i j hj
              simp only [Bool.and_eq_true, beq_iff_eq] at hat
              exact blankFrom_blanked s fuel _ _ (blankRange_blanked h ⟨hat.1, hat.2, hj⟩)
            · exact h
          · split
            · split
              · exact blankFrom_blanked s fuel _ _ h
              · exact h
            · exact blankFrom_blanked s fuel _ _ h

/-- **`blankAnnots` blanks only annotations.** -/
theorem blankAnnots_blanked (s : ByteArray) : Blanked s (blankAnnots s) :=
  blankFrom_blanked s _ _ _ (blanked_refl s)

end Silmaril.Wasm.Tools.Wast
