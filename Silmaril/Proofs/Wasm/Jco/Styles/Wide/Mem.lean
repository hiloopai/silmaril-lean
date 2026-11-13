module

public import Silmaril.Wasm.Jco.Basic.Defs

/-!
# Reading back written bytes

`Mem.read` after `Mem.write`: the bytes just written, and disjoint ranges unchanged. New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Mem

theorem write_eq {m : Mem} {a : Nat} {bs : List UInt8} (h : a + bs.length ≤ m.length) :
    m.write a bs = some (m.take a ++ bs ++ m.drop (a + bs.length)) := by
  simp [Mem.write, h]

theorem getElem?_written {m : Mem} {a : Nat} {bs : List UInt8} (h : a + bs.length ≤ m.length)
    (i : Nat) : (m.take a ++ bs ++ m.drop (a + bs.length))[i]? =
      if i < a then m[i]? else if i < a + bs.length then bs[i - a]? else m[i]? := by
  have ha : (m.take a).length = a := by simp; omega
  split
  · next h1 => rw [List.append_assoc, List.getElem?_append_left (by omega), List.getElem?_take]; simp [h1]
  · next h1 =>
    rw [List.append_assoc, List.getElem?_append_right (by omega), ha]
    split
    · next h2 => rw [List.getElem?_append_left (by omega)]
    · next h2 =>
      rw [List.getElem?_append_right (by omega), List.getElem?_drop]
      congr 1
      omega

theorem length_written {m : Mem} {a : Nat} {bs : List UInt8} (h : a + bs.length ≤ m.length) :
    (m.take a ++ bs ++ m.drop (a + bs.length)).length = m.length := by
  simp; omega

theorem take_drop_written_same {m : Mem} {a : Nat} {bs : List UInt8}
    (h : a + bs.length ≤ m.length) :
    ((m.take a ++ bs ++ m.drop (a + bs.length)).drop a).take bs.length = bs := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_drop, getElem?_written h]
  by_cases hi : i < bs.length
  · have h1 : ¬ a + i < a := by omega
    have h2 : a + i < a + bs.length := by omega
    simp [hi, h1, h2]
  · simp [hi]

theorem take_drop_written_disj {m : Mem} {a : Nat} {bs : List UInt8}
    (h : a + bs.length ≤ m.length) {c n : Nat} (hd : c + n ≤ a ∨ a + bs.length ≤ c) :
    ((m.take a ++ bs ++ m.drop (a + bs.length)).drop c).take n = (m.drop c).take n := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_drop, getElem?_written h, List.getElem?_take,
    List.getElem?_drop]
  by_cases hi : i < n
  · rcases hd with hd | hd
    · simp [hi, (by omega : c + i < a)]
    · have h1 : ¬ c + i < a + bs.length := by omega
      simp [hi, h1]
  · simp [hi]

/-- Reading the bytes just written. -/
theorem read_write_same {m m' : Mem} {a : Nat} {bs : List UInt8} (hw : m.write a bs = some m') :
    m'.read a bs.length = some bs := by
  unfold Mem.write at hw
  split at hw
  · next h =>
    have hm : m' = m.take a ++ bs ++ m.drop (a + bs.length) := (Option.some.inj hw).symm
    rw [hm]
    simp only [Mem.read, length_written h, h, ↓reduceIte, take_drop_written_same h]
  · cases hw

/-- A write leaves disjoint reads alone. -/
theorem read_write_disj {m m' : Mem} {a : Nat} {bs : List UInt8} (hw : m.write a bs = some m')
    {c n : Nat} (hd : c + n ≤ a ∨ a + bs.length ≤ c) : m'.read c n = m.read c n := by
  unfold Mem.write at hw
  split at hw
  · next h =>
    have hm : m' = m.take a ++ bs ++ m.drop (a + bs.length) := (Option.some.inj hw).symm
    rw [hm]
    simp only [Mem.read, length_written h, take_drop_written_disj h hd]
  · cases hw

/-- A write keeps the length. -/
theorem write_length {m m' : Mem} {a : Nat} {bs : List UInt8} (hw : m.write a bs = some m') :
    m'.length = m.length := by
  unfold Mem.write at hw
  split at hw
  · next h => rw [← Option.some.inj hw, length_written h]
  · cases hw

end Silmaril.Wasm.Jco.Mem
