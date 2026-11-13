module

public import Silmaril.Wasm.KernelEval.CoreMem
public import Silmaril.Proofs.Wasm.KernelEval.Memories

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: Core's memory, proofs

Statements in `Silmaril.Wasm.KernelEval.CoreMemThms`.
-/

namespace Silmaril.Proofs.Wasm.KernelEval

open Silmaril.Wasm.KernelEval Silmaril.Wasm.Execution Silmaril.Wasm.Verify.Kernel

theorem dropX_eq' {α : Type} (l : List α) (n : Nat) :
    dropX l n = if n ≤ l.length then some (l.drop n) else none := by
  induction l generalizing n with
  | nil => cases n <;> simp [dropX]
  | cons a l ih => cases n <;> simp_all [dropX]

theorem takeX_eq' {α : Type} (l : List α) (n : Nat) :
    takeX l n = if n ≤ l.length then some (l.take n) else none := by
  induction l generalizing n with
  | nil => cases n <;> simp [takeX]
  | cons a l ih =>
    cases n with
    | zero => simp [takeX]
    | succ n => simp only [takeX] at *; rw [ih]; by_cases h : n ≤ l.length <;> simp [h]

theorem lenGe_eq' {α : Type} (l : List α) (n : Nat) : lenGe l n = decide (n ≤ l.length) := by
  induction l generalizing n with
  | nil => cases n <;> simp [lenGe]
  | cons a l ih => cases n <;> simp_all [lenGe]

theorem overL_eq' {α : Type} (l bs : List α) (h : bs.length ≤ l.length) :
    overL l bs = bs ++ l.drop bs.length := by
  induction l generalizing bs with
  | nil => cases bs <;> simp_all [overL]
  | cons a l ih => cases bs <;> simp_all [overL]

theorem writeL_eq' {α : Type} (l : List α) (n : Nat) (bs : List α)
    (h : n + bs.length ≤ l.length) : writeL l n bs = l.take n ++ bs ++ l.drop (n + bs.length) := by
  induction l generalizing n with
  | nil => simp at h; obtain ⟨rfl, h⟩ := h; simp_all [writeL]
  | cons a l ih =>
    cases n with
    | zero =>
      change overL (a :: l) bs = _
      rw [overL_eq' _ _ (by simpa using h)]; simp
    | succ n =>
      change a :: writeL l n bs = _
      rw [ih n (by simp at h; omega)]; simp [Nat.add_right_comm]

theorem decodeLE_list (bs : List UInt8) :
    Memory.decodeLE ⟨⟨bs⟩⟩ = ListMem.pack (bs.map UInt8.toBitVec) := by
  have : Memory.decodeLE ⟨⟨bs⟩⟩ = bs.foldr (fun byte rest => byte.toNat + 256 * rest) 0 := by
    simp [Memory.decodeLE]
  rw [this]; clear this
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [ListMem.pack, ih]

theorem encodeLE_list : ∀ (k n : Nat),
    (Memory.encodeLE k n).data.toList.map UInt8.toBitVec = ListMem.encode k n
  | 0, _ => rfl
  | k + 1, n => by
    simp only [Memory.encodeLE, ListMem.encode]
    rw [ByteArray.data_append, Array.toList_append, List.map_append, encodeLE_list k (n / 256)]
    simp [UInt8.toBitVec_ofNat']

theorem encode_mod : ∀ (k v : Nat), ListMem.encode k (v % 256 ^ k) = ListMem.encode k v
  | 0, _ => rfl
  | k + 1, v => by
    simp only [ListMem.encode]
    rw [show 256 ^ (k + 1) = 256 * 256 ^ k by rw [Nat.pow_succ, Nat.mul_comm],
      Nat.mod_mul_right_div_self, encode_mod k (v / 256)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp

theorem memSim_kMem : MemSim (fun m : KMem => toListMem m.bytes) where
  load m a k := by
    rcases m with ⟨⟨⟨L⟩⟩⟩
    simp only [MemOps.load, toListMem, fload, dropX_eq', takeX_eq', List.length_map]
    by_cases h : a + k ≤ L.length
    · rw [iteT h, iteT (show a ≤ L.length by omega)]
      rw [Option.bind_some, iteT (show k ≤ (L.drop a).length by simp; omega)]
      simp only [Option.map_some, BitVec.toNat_ofNat, decodeLE_list, two_pow_eight_mul,
        Option.some.injEq, List.map_take, List.map_drop]
      have := pack_lt (((L.map UInt8.toBitVec).drop a).take k)
      simp only [List.length_take, List.length_drop, List.length_map] at this
      rw [Nat.mod_eq_of_lt (by rwa [Nat.min_eq_left (by omega)] at this)]
    · rw [iteF h]
      by_cases h2 : a ≤ L.length
      · rw [iteT h2, Option.bind_some, iteF (show ¬ k ≤ (L.drop a).length by simp; omega)]; rfl
      · simp [iteF h2]
  store m a k v := by
    rcases m with ⟨⟨⟨L⟩⟩⟩
    simp only [MemOps.store, toListMem, fstore, lenGe_eq', List.length_map]
    by_cases h : a + k ≤ L.length
    · simp only [h, decide_true, ↓reduceIte, Option.map_some, Option.some.injEq]
      have hs : (Memory.encodeLE k (BitVec.ofNat (8 * k) v).toNat).data.toList.length = k := by
        simp
      rw [writeL_eq' _ _ _ (by rw [hs]; exact h), hs]
      simp only [List.map_append, List.map_take, List.map_drop, ListMem.mk.injEq]
      rw [encodeLE_list, BitVec.toNat_ofNat, two_pow_eight_mul, encode_mod]
    · simp [h]

theorem kmem_load_eq (m : Memory.Bytes) (a k : Nat) :
    MemOps.load (KMem.mk m) a k = MemOps.load (CoreMem.mk m) a k := by
  simp only [MemOps.load, fload_eq]

theorem kmem_store_eq (m : Memory.Bytes) (a k v : Nat) :
    (MemOps.store (KMem.mk m) a k v).map KMem.bytes =
      (MemOps.store (CoreMem.mk m) a k v).map CoreMem.bytes := by
  simp only [MemOps.store, fstore_eq, Option.map_map]; rfl

theorem memSim_coreMem : MemSim (fun m : CoreMem => toListMem m.bytes) where
  load m a k := by
    rw [← kmem_load_eq]; exact memSim_kMem.load ⟨m.bytes⟩ a k
  store m a k v := by
    have h1 := memSim_kMem.store ⟨m.bytes⟩ a k v
    have h2 := kmem_store_eq m.bytes a k v
    simp only at h1
    rw [h1]
    have : ∀ o : Option KMem, o.map (fun m => toListMem m.bytes) =
        (o.map KMem.bytes).map toListMem := fun o => by cases o <;> rfl
    have h3 : ∀ o : Option CoreMem, o.map (fun m => toListMem m.bytes) =
        (o.map CoreMem.bytes).map toListMem := fun o => by cases o <;> rfl
    rw [this, h2, ← h3]

end Silmaril.Proofs.Wasm.KernelEval
