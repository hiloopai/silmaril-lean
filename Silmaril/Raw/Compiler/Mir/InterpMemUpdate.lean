module

public import Silmaril.Compiler.Mir.InterpMem.Defs
@[expose] public section

/-! # Paged-memory updates and their semantic view -/

namespace Silmaril.Compile.Mir.Interp.Mem

open Silmaril.Machine

private theorem pageIndex_lt (size a : Nat) (ha : a < size) :
    a >>> pageBits < (size + pageSize - 1) / pageSize := by
  simp only [pageBits, pageSize, Nat.shiftRight_eq_div_pow]
  omega

private theorem page_read_set (pg : ByteArray)
    (h : pg.size = 0 ∨ pg.size = pageSize) (a b : Nat) (v : UInt8) :
    let pg' := (if pg.size = 0 then ByteArray.mk (Array.replicate pageSize 0) else pg).set! (a % pageSize) v
    (if pg'.size = 0 then 0 else pg'[b % pageSize]!) =
      if b % pageSize = a % pageSize then v else if pg.size = 0 then 0 else pg[b % pageSize]! := by
  have ha : a % pageSize < pageSize := Nat.mod_lt _ (by decide)
  have hb : b % pageSize < pageSize := Nat.mod_lt _ (by decide)
  rcases h with hz | hf
  · simp only [hz, ite_true]
    have hs : (ByteArray.mk (Array.replicate pageSize 0)).size = pageSize := by
      simp [ByteArray.size]
    simp only [ByteArray.size_set!, hs, show pageSize ≠ 0 by decide, ite_false]
    by_cases he : b % pageSize = a % pageSize
    · rw [he, ByteArray.getElem!_set!_self _ _ _ (by simpa only [hs] using ha)]
      simp
    · rw [ByteArray.getElem!_set!_ne _ _ _ _ (Ne.symm he)]
      rw [getElem!_pos _ _ (by simpa only [hs] using hb)]
      simp [he, ByteArray.getElem_eq_getElem_data]
  · simp only [hf, show pageSize ≠ 0 by decide, ite_false, ByteArray.size_set!]
    by_cases he : b % pageSize = a % pageSize
    · rw [he, ByteArray.getElem!_set!_self _ _ _ (by omega)]
      simp
    · rw [ByteArray.getElem!_set!_ne _ _ _ _ (Ne.symm he)]
      simp [he]

/-- A byte write below the memory bound changes exactly that address. -/
theorem getByte_setByte (m : Mem) (hm : m.WellFormed)
    (hp : m.pages.size = (m.size + pageSize - 1) / pageSize)
    (a : Nat) (v : UInt8) (ha : a < m.size) (b : Nat) :
    (m.setByte a v).getByte b = if b = a then v else m.getByte b := by
  have ha' : a >>> pageBits < m.pages.size := by rw [hp]; exact pageIndex_lt _ _ ha
  rcases m with ⟨size, pages⟩
  change a >>> pageBits < pages.size at ha'
  change ∀ i < pages.size, (pages[i]!).size = 0 ∨ (pages[i]!).size = pageSize at hm
  simp only [setByte, getByte]
  by_cases hpg : b >>> pageBits = a >>> pageBits
  · rw [hpg]
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
    simp only [ite_true, getElem?_pos pages (a >>> pageBits) ha', Option.map_some, Option.getD_some]
    have hw := page_read_set (pages[a >>> pageBits]!) (hm _ ha') a b v
    simp only [getElem!_pos pages (a >>> pageBits) ha'] at hw
    rw [hw]
    have he : b % pageSize = a % pageSize ↔ b = a := by
      constructor
      · intro he
        simp only [pageBits, pageSize, Nat.shiftRight_eq_div_pow] at hpg he
        have h₁ := Nat.mod_add_div b 65536
        have h₂ := Nat.mod_add_div a 65536
        omega
      · rintro rfl; rfl
    simp [he]
  · have hba : b ≠ a := fun he => hpg (he ▸ rfl)
    simp [hba, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_modify, Ne.symm hpg]

@[simp] theorem setByte_size (m : Mem) (a : Nat) (v : UInt8) :
    (m.setByte a v).size = m.size := rfl

@[simp] theorem setByte_pages_size (m : Mem) (a : Nat) (v : UInt8) :
    (m.setByte a v).pages.size = m.pages.size := by
  simp [setByte]

/-- Materializing a zero page and updating a byte preserves page extents. -/
theorem setByte_wellFormed (m : Mem) (hm : m.WellFormed) (a : Nat) (v : UInt8) :
    (m.setByte a v).WellFormed := by
  intro i hi
  have hi' : i < m.pages.size := by simpa using hi
  change ((m.pages.modify (a >>> pageBits) _)[i]!).size = 0 ∨
    ((m.pages.modify (a >>> pageBits) _)[i]!).size = pageSize
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases he : a >>> pageBits = i
  · subst i
    simp only [ite_true, getElem?_pos m.pages (a >>> pageBits) hi', Option.map_some, Option.getD_some]
    right
    have hp := hm _ hi'
    rw [getElem!_pos m.pages _ hi'] at hp
    rw [ByteArray.size_set!]
    split
    · exact Array.size_replicate
    · rename_i hz
      exact hp.resolve_left hz
  · simp only [he, ite_false]
    simpa only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] using hm i hi'

/-- The semantic memory sees a functional update at the written address. -/
theorem setByte_toLir (m : Mem) (hm : m.WellFormed)
    (hp : m.pages.size = (m.size + pageSize - 1) / pageSize)
    (a : Nat) (v : UInt8) (ha : a < m.size) :
    (m.setByte a v).toLir =
      ⟨m.size, fun b => if b = a then v.toBitVec else m.toLir.bytes b⟩ := by
  change Lir.Memory.mk m.size _ = Lir.Memory.mk m.size _
  congr 1
  funext b
  rw [getByte_setByte m hm hp a v ha b]
  split
  · apply BitVec.eq_of_toNat_eq
    simp
  · rfl

end Silmaril.Compile.Mir.Interp.Mem
