module

public import Silmaril.Compiler.Mir.InterpMemImage.Defs
@[expose] public section

/-! # Image initialization without a fit premise

Out-of-bounds image bytes are discarded, so the semantic view agrees with
`Mir.initMem` only below the configured bound. That is sufficient for stuckness.
-/

namespace Silmaril.Compile.Mir.Interp.Mem

private def imagePrefixAny (size base : Nat) (image : ByteArray) (n : Nat) : Mem :=
  (List.range n).foldl
    (fun m i => if base+i < size then m.setByte (base+i) image[i]! else m) (zero size)

private theorem imagePrefixAny_spec (size base : Nat) (image : ByteArray)
    (n : Nat) (hn : n ≤ image.size) :
    let m := imagePrefixAny size base image n
    m.WellFormed ∧ m.size = size ∧
      m.pages.size = (size + pageSize - 1) / pageSize ∧
      ∀ b, m.getByte b =
        if base ≤ b ∧ b < base+n ∧ b < size then image[b-base]! else 0 := by
  induction n with
  | zero =>
    simp only [imagePrefixAny, List.range_zero, List.foldl_nil, Nat.add_zero]
    refine ⟨zero_wellFormed _, rfl, by simp only [zero, Array.size_replicate], ?_⟩
    intro b
    rw [getByte_zero, ite_eq_right (by omega)]
  | succ n ih =>
    obtain ⟨hw, hs, hp, hb⟩ := ih (by omega)
    have he : imagePrefixAny size base image (n+1) =
        if base+n < size then (imagePrefixAny size base image n).setByte (base+n) image[n]!
        else imagePrefixAny size base image n := by
      simp [imagePrefixAny, List.range_succ, List.foldl_append]
    rw [he]
    by_cases ha : base+n < size
    · simp only [ha, ite_true]
      refine ⟨setByte_wellFormed _ hw _ _, hs, ?_, ?_⟩
      · simpa using hp
      · intro b
        rw [getByte_setByte _ hw (by simpa [hs] using hp) _ _ (by simpa [hs] using ha), hb]
        by_cases h : b = base+n
        · subst b
          simp [ha]
        · have hr : (base ≤ b ∧ b < base+(n+1) ∧ b < size) ↔
              (base ≤ b ∧ b < base+n ∧ b < size) := by omega
          simp [h, hr]
    · simp only [ha, ite_false]
      refine ⟨hw, hs, hp, ?_⟩
      intro b
      rw [hb]
      have hr : (base ≤ b ∧ b < base+(n+1) ∧ b < size) ↔
          (base ≤ b ∧ b < base+n ∧ b < size) := by omega
      simp only [hr]

theorem ofImage_invariants_any (size base : Nat) (image : ByteArray) :
    (ofImage size base image).WellFormed ∧
      (ofImage size base image).size = size ∧
      (ofImage size base image).pages.size = (size + pageSize - 1) / pageSize := by
  rw [ofImage_eq_foldl]
  have h := imagePrefixAny_spec size base image image.size (by omega)
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem getByte_ofImage_any (size base : Nat) (image : ByteArray) (b : Nat) :
    (ofImage size base image).getByte b =
      if base ≤ b ∧ b < base+image.size ∧ b < size then image[b-base]! else 0 := by
  rw [ofImage_eq_foldl]
  exact (imagePrefixAny_spec size base image image.size (by omega)).2.2.2 b

end Silmaril.Compile.Mir.Interp.Mem
