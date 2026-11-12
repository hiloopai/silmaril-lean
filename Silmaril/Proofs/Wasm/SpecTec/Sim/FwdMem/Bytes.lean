module

public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Defs

/-!
# Core's little-endian byte encoding, on images

What the load and store rules need of `Silmaril.Wasm.Execution.Memory.load`/`store`, on the
encoded byte lists `bytesV`:

* `load_bytesV`: a successful `k`-byte load reads a word whose `k`-byte encoding is the slice
  `bytes[i : k]` of the image (`encodeLE k ∘ decodeLE` is the identity on `k`-byte strings,
  `encL_decL`);
* `store_bytesV`: a successful store writes the image `bytes[0 : i] ++ enc ++ bytes[i + k :]`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdMem

open Silmaril.Wasm.Execution.Memory

/-! ## List forms of the encoders -/

/-- `encodeLE`, on lists. -/
def encL : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat n :: encL k (n / 256)

/-- `decodeLE`, on lists. -/
def decL (l : List UInt8) : Nat := l.foldr (fun b r => b.toNat + 256 * r) 0

theorem encodeLE_toList (k n : Nat) : (encodeLE k n).data.toList = encL k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [encodeLE, ByteArray.toList_data_append, ih]
    rfl

theorem decodeLE_eq (b : ByteArray) : decodeLE b = decL b.data.toList := by
  rw [decodeLE, decL, Array.foldr_toList]

theorem uInt8_ofNat_add (x : UInt8) (r : Nat) : UInt8.ofNat (x.toNat + 256 * r) = x := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat']
  have := x.toNat_lt
  omega

/-- `encodeLE ∘ decodeLE` is the identity on byte strings of the given length. -/
theorem encL_decL : ∀ l : List UInt8, encL l.length (decL l) = l
  | [] => rfl
  | x :: l => by
    have hx := x.toNat_lt
    have hd : (x.toNat + 256 * decL l) / 256 = decL l := by omega
    simp only [List.length_cons, encL, decL, List.foldr_cons] at hd ⊢
    rw [uInt8_ofNat_add, hd]
    exact congrArg _ (encL_decL l)

theorem decL_lt : ∀ l : List UInt8, decL l < 256 ^ l.length
  | [] => by simp [decL]
  | x :: l => by
    have hx := x.toNat_lt
    have ih := decL_lt l
    simp only [decL, List.foldr_cons, List.length_cons, Nat.pow_succ] at ih ⊢
    have h1 : 256 * List.foldr (fun b r => b.toNat + 256 * r) 0 l + 256 ≤
        256 * 256 ^ l.length := by
      have := Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt ih)
      omega
    omega

/-! ## Images of byte strings -/

theorem bytesV_eq (b : ByteArray) :
    bytesV b = b.data.toList.map fun c => Silmaril.SpecTec.Equiv.Execution.pctV c.toNat := rfl

@[simp] theorem bytesV_length (b : ByteArray) : (bytesV b).length = b.size := by
  rw [bytesV_eq, List.length_map, Array.length_toList]
  rfl

theorem bytesV_append (a b : ByteArray) : bytesV (a ++ b) = bytesV a ++ bytesV b := by
  rw [bytesV_eq, ByteArray.toList_data_append, List.map_append]
  rfl

theorem bytesV_extract (b : ByteArray) (i j : Nat) :
    bytesV (b.extract i j) = ((bytesV b).drop i).take (j - i) := by
  rw [bytesV_eq, ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    List.map_take, List.map_drop]
  rfl

theorem leBytesV_length (k n : Nat) : (leBytesV k n).length = k := by
  rw [leBytesV, bytesV_length, encodeLE_size]

/-- A successful `k`-byte load at `i` reads a word whose encoding is the slice of the image. -/
theorem load_bytesV {mem : ByteArray} {i k : Nat} {c : BitVec (8 * k)}
    (h : load mem i k = some c) :
    i + k ≤ mem.size ∧ leBytesV k c.toNat = ((bytesV mem).drop i).take k := by
  simp only [load, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  obtain ⟨hb, rfl⟩ := (readBytes_eq_some_iff mem e i k).1 he
  refine ⟨hb, ?_⟩
  set e := mem.extract i (i + k) with he_def
  have hlen : e.data.toList.length = k := by
    rw [Array.length_toList, ByteArray.size_data, he_def, ByteArray.size_extract]
    omega
  have hpow : (2 : Nat) ^ (8 * k) = 256 ^ k := by rw [Nat.pow_mul]
  have hlt : decodeLE e < 2 ^ (8 * k) := by
    rw [decodeLE_eq, hpow]
    have := decL_lt e.data.toList
    rwa [hlen] at this
  have hed := encL_decL e.data.toList
  rw [hlen] at hed
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, leBytesV, bytesV_eq, encodeLE_toList,
    decodeLE_eq, hed, ← bytesV_eq, he_def, bytesV_extract, Nat.add_sub_cancel_left]

/-- A successful `k`-byte store at `i` writes the encoding into the image. -/
theorem store_bytesV {mem b : ByteArray} {i k : Nat} {w : BitVec (8 * k)}
    (h : store mem i w = some b) :
    i + k ≤ mem.size ∧
      bytesV b = (bytesV mem).take i ++ leBytesV k w.toNat ++ (bytesV mem).drop (i + k) := by
  obtain ⟨hb, rfl⟩ := (writeBytes_eq_some_iff mem _ b i).1 h
  rw [encodeLE_size] at hb ⊢
  refine ⟨hb, ?_⟩
  rw [bytesV_append, bytesV_append, bytesV_extract, bytesV_extract, leBytesV, Nat.sub_zero,
    List.drop_zero]
  congr 1
  exact List.take_of_length_le (by rw [List.length_drop, bytesV_length])

end Silmaril.Wasm.SpecTec.Sim.FwdMem
