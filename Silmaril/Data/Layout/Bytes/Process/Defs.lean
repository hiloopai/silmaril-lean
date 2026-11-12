module

public import Silmaril.Data.Layout.Bytes.Thms
public import Silmaril.Process.Memory

/-!
# Byte views over x86 process memories

`Silmaril.Process.Memory` is the memory of the x86 machine models (`Silmaril.X86.MState` and
its extensions): mapped regions with permissions over a byte map
`ByteMemory` (`Std.ExtHashMap Nat (BitVec 8)`). The struct lenses act on the byte map; the
permission checks stay with `Memory.readBytes`/`Memory.writeBytes`, which agree with the lens
reads and writes (`read_of_readBytes`, `get?_writeBytes`).
-/

@[expose] public section

namespace Silmaril.Data.Layout

open Silmaril.Process

instance : ByteMem ByteMemory where
  get? m a := m.get? a
  set m a v := m.insert a v
  get?_set_self _ _ _ _ := by simp
  get?_set_ne _ a b _ h := by
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    simp [h]

/-- Lens reads and writes of a process memory act on its byte map and keep its mappings. -/
instance : ByteMem Memory where
  get? m a := m.bytes.get? a
  set m a v := { m with bytes := m.bytes.insert a v }
  get?_set_self _ _ _ _ := by simp
  get?_set_ne _ a b _ h := by
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    simp [h]

namespace ProcessBytes

theorem get?_write (m : ByteMemory) (a : Nat) (bs : List Byte) (x : Nat) :
    (ByteMem.write m a bs).get? x = if a ≤ x ∧ x < a + bs.length then bs[x - a]? else m.get? x := by
  induction bs generalizing m a with
  | nil => simp [ByteMem.write]
  | cons b bs ih =>
    simp only [ByteMem.write]
    rw [ih]
    show (if _ then _ else (m.insert a b).get? x) = _
    rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    by_cases hx : x = a
    · subst hx; simp
    · have : (a == x) = false := by simp; omega
      rw [this]
      by_cases hin : a + 1 ≤ x ∧ x < a + 1 + bs.length
      · have h2 : a ≤ x ∧ x < a + (bs.length + 1) := by omega
        simp only [hin, h2, and_self, ite_true, List.length_cons]
        rw [show x - a = (x - (a + 1)) + 1 by omega]; simp
      · have h2 : ¬ (a ≤ x ∧ x < a + (bs.length + 1)) := by omega
        simp only [hin, h2, ite_false, List.length_cons, Bool.false_eq_true]
        rw [Std.ExtHashMap.get?_eq_getElem?]

theorem get?_install (m : ByteMemory) (a : Nat) (bs : List Byte) (x : Nat) :
    (Memory.install m a bs).get? x = if a ≤ x ∧ x < a + bs.length then bs[x - a]? else m.get? x := by
  by_cases h : a ≤ x ∧ x < a + bs.length
  · simp only [h, and_self, ite_true]
    have := Memory.install_get m a bs (x - a) (by omega)
    rw [show a + (x - a) = x by omega] at this
    rw [this]; simp
  · simp only [h, ite_false]
    rw [Memory.install_outside m a bs x (by omega)]

end ProcessBytes

/-- The lens write of a process memory installs the same bytes as `Memory.install`. -/
theorem bytes_write (m : Memory) (a : Nat) (bs : List Byte) :
    ∀ x, (ByteMem.write m a bs).bytes.get? x = (Memory.install m.bytes a bs).get? x := by
  intro x
  rw [ProcessBytes.get?_install]
  have : ∀ (m : Memory) a, (ByteMem.write m a bs).bytes = ByteMem.write m.bytes a bs := by
    induction bs with
    | nil => intro m a; rfl
    | cons b bs ih => intro m a; exact ih _ _
  rw [this, ProcessBytes.get?_write]

theorem regions_write (m : Memory) (a : Nat) (bs : List Byte) :
    (ByteMem.write m a bs).regions = m.regions := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih => exact ih _ _

theorem read_eq_readBacking (m : Memory) (a n : Nat) :
    ByteMem.read m a n = Memory.readBacking m.bytes a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [ByteMem.read, Memory.readBacking, ih]
    show (match m.bytes.get? a, _ with | some b, some bs => some (b :: bs) | _, _ => none) = _
    cases m.bytes.get? a <;> cases Memory.readBacking m.bytes (a + 1) n <;> rfl

/-- A permitted read of the machine is a lens read. -/
theorem read_of_readBytes {m : Memory} {a n : Nat} {bs : List Byte}
    (h : m.readBytes a n = some bs) : ByteMem.read m a n = some bs := by
  simp only [Memory.readBytes, Memory.readWith] at h
  split at h
  · rw [read_eq_readBacking]; exact h
  · cases h

/-- A permitted write of the machine has the bytes and mappings of the lens write. -/
theorem get?_writeBytes {m m' : Memory} {a : Nat} {bs : List Byte}
    (h : m.writeBytes a bs = some m') :
    m'.regions = (ByteMem.write m a bs).regions ∧
      ∀ x, m'.bytes.get? x = (ByteMem.write m a bs).bytes.get? x := by
  simp only [Memory.writeBytes] at h
  split at h
  · cases h
    exact ⟨(regions_write m a bs).symm, fun x => (bytes_write m a bs x).symm⟩
  · cases h

end Silmaril.Data.Layout
