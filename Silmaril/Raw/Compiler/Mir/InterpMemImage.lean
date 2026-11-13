module

public import Silmaril.Compiler.Mir.InterpMemUpdate.Defs
public import Init.Data.Range.Lemmas

@[expose] public section

/-! # Image initialization under the memory-fit premise -/

namespace Silmaril.Compile.Mir.Interp.Mem

open Silmaril.Machine

theorem ofImage_eq_foldl (size base : Nat) (image : ByteArray) :
    ofImage size base image = (List.range image.size).foldl
      (fun m i => if base + i < size then m.setByte (base + i) image[i]! else m)
      (zero size) := by
  have body (i : Nat) (m : Mem) :
      (if base + i < size then pure (ForInStep.yield (m.setByte (base+i) image[i]!))
        else pure (ForInStep.yield m) : Id (ForInStep Mem)) =
      pure (ForInStep.yield (if base+i < size then m.setByte (base+i) image[i]! else m)) := by
    split <;> rfl
  simp [ofImage, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ← List.range_eq_range', body]

private def imagePrefix (size base : Nat) (image : ByteArray) (n : Nat) : Mem :=
  (List.range n).foldl
    (fun m i => if base + i < size then m.setByte (base + i) image[i]! else m)
    (zero size)

private theorem imagePrefix_spec (size base : Nat) (image : ByteArray)
    (fit : ∀ i < image.size, base + i < size) (n : Nat) (hn : n ≤ image.size) :
    let m := imagePrefix size base image n
    m.WellFormed ∧ m.size = size ∧
      m.pages.size = (size + pageSize - 1) / pageSize ∧
      ∀ b, m.getByte b = if base ≤ b ∧ b < base + n then image[b - base]! else 0 := by
  induction n with
  | zero =>
    simp only [imagePrefix, List.range_zero, List.foldl_nil, Nat.add_zero]
    refine ⟨zero_wellFormed _, rfl, by simp only [zero, Array.size_replicate], ?_⟩
    intro b
    rw [getByte_zero, ite_eq_right (by omega)]
  | succ n ih =>
    have hn' : n < image.size := by omega
    obtain ⟨hw, hs, hp, hb⟩ := ih (by omega)
    have hf := fit n hn'
    have he : imagePrefix size base image (n+1) =
        (imagePrefix size base image n).setByte (base+n) image[n]! := by
      simp [imagePrefix, List.range_succ, List.foldl_append, hf]
    rw [he]
    refine ⟨setByte_wellFormed _ hw _ _, hs, ?_, ?_⟩
    · simpa using hp
    · intro b
      rw [getByte_setByte _ hw (by simpa [hs] using hp) _ _ (by simpa [hs] using hf), hb]
      by_cases h : b = base+n
      · subst b
        simp
      · have hr : (base ≤ b ∧ b < base+(n+1)) ↔ (base ≤ b ∧ b < base+n) := by omega
        simp [h, hr]

/-- Image initialization preserves the page invariant. -/
theorem ofImage_wellFormed (size base : Nat) (image : ByteArray)
    (fit : ∀ i < image.size, base + i < size) :
    (ofImage size base image).WellFormed := by
  rw [ofImage_eq_foldl]
  exact (imagePrefix_spec size base image fit image.size (by omega)).1

/-- The initialized memory has the configured extent and the corresponding page count. -/
theorem ofImage_extents (size base : Nat) (image : ByteArray)
    (fit : ∀ i < image.size, base + i < size) :
    (ofImage size base image).size = size ∧
      (ofImage size base image).pages.size = (size + pageSize - 1) / pageSize := by
  rw [ofImage_eq_foldl]
  have h := imagePrefix_spec size base image fit image.size (by omega)
  exact ⟨h.2.1, h.2.2.1⟩

/-- Every initialized byte, including inaccessible bytes, agrees under image fit. -/
theorem getByte_ofImage (size base : Nat) (image : ByteArray)
    (fit : ∀ i < image.size, base + i < size) (b : Nat) :
    (ofImage size base image).getByte b =
      if base ≤ b ∧ b < base + image.size then image[b - base]! else 0 := by
  rw [ofImage_eq_foldl]
  exact (imagePrefix_spec size base image fit image.size (by omega)).2.2.2 b

theorem ofImage_toLir (cfg : Config) (l : Linked)
    (fit : ∀ i < l.image.size, l.dataBase + i < cfg.memSize) :
    (Interp.initMem cfg l).toLir = Mir.initMem cfg l := by
  have h := imagePrefix_spec cfg.memSize l.dataBase l.image fit l.image.size (by omega)
  have hs : (ofImage cfg.memSize l.dataBase l.image).size = cfg.memSize := by
    rw [ofImage_eq_foldl]; exact h.2.1
  apply congrArg₂ Lir.Memory.mk hs
  funext b
  change BitVec.ofNat 8 ((ofImage cfg.memSize l.dataBase l.image).getByte b).toNat = _
  rw [getByte_ofImage _ _ _ fit]
  by_cases hb : l.dataBase ≤ b ∧ b < l.dataBase + l.image.size
  · rw [ite_eq_left hb, ite_eq_left hb]
    have hi : b-l.dataBase < l.image.size := by omega
    have he : l.image[b-l.dataBase]! = l.image.get! (b-l.dataBase) := by
      rcases him : l.image with ⟨xs⟩
      rw [him] at hi
      rw [getElem!_pos (ByteArray.mk xs) (b-l.dataBase) hi]
      change xs[b-l.dataBase] = xs[b-l.dataBase]!
      exact (getElem!_pos xs _ hi).symm
    rw [he]
  · simp [hb]

end Silmaril.Compile.Mir.Interp.Mem
