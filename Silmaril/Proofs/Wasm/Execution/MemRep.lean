module

public import Silmaril.Wasm.Execution.MemRep.Defs
public import Silmaril.Prelude.Bytes.Digits.Thms

/-! Proofs for `Silmaril.Wasm.Execution.MemRep.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Execution.MemRep

open Silmaril.Wasm.Execution Silmaril.KBytes

theorem decodeLE_eq (b : ByteArray) : Memory.decodeLE b = leVal b.data.toList := by
  unfold Memory.decodeLE
  rw [← Array.foldr_toList]
  generalize b.data.toList = l
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.foldr_cons, leVal, ih]

theorem encodeLE_toList : ∀ (n v : Nat), (Memory.encodeLE n v).data.toList = unpack n v
  | 0, _ => rfl
  | n + 1, v => by
    simp [Memory.encodeLE, unpack, ByteArray.data_append, encodeLE_toList n (v / 256)]

theorem toList_toBytes (m : KMem) : (KMem.toBytes m).data.toList = m.t.toList := rfl

theorem size_toBytes (m : KMem) : (KMem.toBytes m).size = m.t.len := by
  rw [← ByteArray.size_data, ← Array.length_toList, toList_toBytes, length_toList _ m.wf]

theorem toList_extract (b : ByteArray) (a c : Nat) :
    (b.extract a c).data.toList = (b.data.toList.drop a).take (c - a) := by
  simp [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]

theorem readBytes_eq (m : KMem) (a count : Nat) :
    KMem.readBytes m a count = Memory.readBytes (KMem.toBytes m) a count := by
  unfold KMem.readBytes Memory.readBytes
  rw [size_toBytes]
  split
  · congr 1
    apply ByteArray.ext; apply Array.toList_inj.mp
    rw [toList_extract, toList_toBytes]; simp
  · rfl

theorem load_eq (m : KMem) (a count : Nat) :
    KMem.load m a count = Memory.load (KMem.toBytes m) a count := by
  unfold KMem.load Memory.load
  rw [← readBytes_eq, readLE_eq _ m.wf, length_toList _ m.wf]
  unfold KMem.readBytes
  split <;> simp [decodeLE_eq]

theorem writeBytes_eq (m : KMem) (a : Nat) (bs : ByteArray) :
    (KMem.writeBytes m a bs).map KMem.toBytes = Memory.writeBytes (KMem.toBytes m) a bs := by
  unfold KMem.writeBytes
  by_cases h : a + bs.size ≤ m.t.len
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    have h' : a + bs.size ≤ (KMem.toBytes m).size := by rw [size_toBytes]; exact h
    rw [(Memory.writeBytes_eq_some_iff (KMem.toBytes m) bs _ a).mpr ⟨h', rfl⟩]
    simp only [Option.map_some, Option.some.injEq]
    apply ByteArray.ext; apply Array.toList_inj.mp
    have hl : bs.data.toList.length = bs.size := by simp [ByteArray.size_data]
    show (m.t.write a bs.size (leVal bs.data.toList)).toList = _
    rw [toList_write _ _ _ _ m.wf h, splice, ← hl, unpack_leVal]
    simp only [ByteArray.data_append, Array.toList_append, toList_extract, toList_toBytes,
      List.drop_zero, Nat.sub_zero, size_toBytes, hl]
    rw [List.take_of_length_le (l := List.drop (a + bs.size) m.t.toList)
      (by rw [List.length_drop, length_toList _ m.wf])]
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    simp [Memory.writeBytes, size_toBytes, h]

theorem store_eq (m : KMem) (a : Nat) {count : Nat} (w : BitVec (8 * count)) :
    (KMem.store m a w).map KMem.toBytes = Memory.store (KMem.toBytes m) a w :=
  writeBytes_eq m a _

theorem grow_eq (m : KMem) (maximum : Option Nat) (delta : Nat) :
    (KMem.grow? m maximum delta).map KMem.toBytes =
      Memory.grow? (KMem.toBytes m) maximum delta := by
  unfold KMem.grow? Memory.grow? Memory.size
  rw [size_toBytes]
  split
  · simp only [Option.map_some, Option.some.injEq]
    apply ByteArray.ext; apply Array.toList_inj.mp
    show (m.t ++ (KMem.zeros _).t).toList = _
    rw [toList_append]
    simp [toList_toBytes, KMem.zeros, toList_zerosCanon _ _ (by decide : 0 < KMem.leafBytes),
      ByteArray.data_append]
  · rfl

theorem zeros_eq (n : Nat) : (KMem.toBytes (KMem.zeros n)).data.toList = List.replicate n 0 := by
  rw [toList_toBytes]
  exact toList_zerosCanon _ _ (by decide)

end Silmaril.Proofs.Wasm.Execution.MemRep
