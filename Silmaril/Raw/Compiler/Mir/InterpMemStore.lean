module

public import Silmaril.Compiler.Mir.InterpMemWord.Defs
@[expose] public section

/-! # Little-endian writes preserve the semantic memory -/

namespace Silmaril.Compile.Mir.Interp.Mem

open Silmaril.Machine

private theorem writeLE_eq_foldl (m : Mem) (a n : Nat) (v : UInt64) :
    m.writeLE a n v = (List.range n).foldl
      (fun m i => m.setByte (a+i) (v >>> (8*i).toUInt64).toUInt8) m := by
  simp [writeLE, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ← List.range_eq_range']

private theorem writeLE_succ (m : Mem) (a n : Nat) (v : UInt64) :
    m.writeLE a (n+1) v =
      (m.writeLE a n v).setByte (a+n) (v >>> (8*n).toUInt64).toUInt8 := by
  simp [writeLE_eq_foldl, List.range_succ, List.foldl_append]

private theorem byte_shift (v : UInt64) (i : Nat) (hi : i < 8) :
    (v >>> (8*i).toUInt64).toUInt8.toBitVec = LittleEndian.wordByte v.toBitVec i := by
  have h : 8*i < 64 := by omega
  simp [LittleEndian.wordByte, UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq',
    Nat.mod_eq_of_lt h]

/-- Writing at most eight bytes preserves all memory invariants and agrees with Lir. -/
theorem writeLE_spec (m : Mem) (hw : m.WellFormed)
    (hp : m.pages.size = (m.size + pageSize - 1) / pageSize)
    (a n : Nat) (v : UInt64) (h8 : n ≤ 8) (hn : a+n ≤ m.size) :
    let m' := m.writeLE a n v
    m'.WellFormed ∧ m'.size = m.size ∧ m'.pages.size = m.pages.size ∧
      m'.toLir.bytes = Lir.writeLE m.toLir.bytes a n v.toBitVec := by
  induction n with
  | zero =>
    simp only [writeLE_eq_foldl, List.range_zero, List.foldl_nil]
    refine ⟨hw, trivial, trivial, ?_⟩
    funext b
    simp [Lir.writeLE]
  | succ n ih =>
    obtain ⟨hw', hs, hp', hb⟩ := ih (by omega) (by omega)
    rw [writeLE_succ]
    refine ⟨setByte_wellFormed _ hw' _ _, hs, ?_, ?_⟩
    · simpa using hp'
    · rw [setByte_toLir _ hw' (by simpa [hs, hp'] using hp) _ _ (by omega)]
      funext b
      change (if b = a+n then _ else _) = _
      rw [hb]
      by_cases he : b = a+n
      · subst b
        simp only [ite_true, Lir.writeLE]
        rw [ite_eq_left (by omega)]
        simpa using byte_shift v n (by omega)
      · have hr : (a ≤ b ∧ b < a+(n+1)) ↔ (a ≤ b ∧ b < a+n) := by omega
        simp [he, Lir.writeLE, hr]

/-- A successful Lir store returns exactly the executable memory's semantic view. -/
theorem store_toLir (m : Mem) (hw : m.WellFormed)
    (hp : m.pages.size = (m.size + pageSize - 1) / pageSize)
    (w : Lir.Width) (a : Nat) (v : UInt64) :
    m.toLir.store w a v.toBitVec =
      if a+w.bytes ≤ m.size then some (m.writeLE a w.bytes v).toLir else none := by
  by_cases h : a+w.bytes ≤ m.size
  · obtain ⟨_, hs, _, hb⟩ := writeLE_spec m hw hp a w.bytes v
      (by cases w <;> decide) h
    simp only [h, ite_true, Lir.Memory.store, Lir.Memory.InBounds, toLir]
    congr 1
    exact congrArg₂ Lir.Memory.mk hs.symm hb.symm
  · simp [Lir.Memory.store, Lir.Memory.InBounds, toLir, h]

end Silmaril.Compile.Mir.Interp.Mem
