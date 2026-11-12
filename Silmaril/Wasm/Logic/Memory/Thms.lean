module

public import Silmaril.Wasm.Logic.Memory.Defs

/-!
# A linear-memory model for program proofs: lemmas

Wasm linear memory is a `ByteArray`; `Memory.load`/`Memory.store` read and write
little-endian words at byte addresses, failing out of bounds. Program proofs want
to talk about **regions** (byte ranges), **separation** (a store to one region
leaves a disjoint region unchanged), and the **little-endian encodings** of
`i32`/`i64` words. The definitions are in `Silmaril.Wasm.Logic.Memory.Defs`. Provided:

* `Region` (a base and a length), `Region.Disjoint`, `Region.InBounds`, and
  `bytesAt B r` (the bytes of `B` in `r`, as a list);
* `leNat` (the little-endian value of a byte list) and `u32le`/`u64le` (the
  little-endian bytes of a word), with `leNat_u32le`/`leNat_u64le`;
* the access lemmas: `load_eq` (an in-bounds load is the little-endian value of
  the region), `store_eq` and `size_store`, `load_store_same`,
  `load_store_disjoint` and `bytesAt_store_disjoint` (separation);
* `bytesAt_writeBytes` for the host writing an input (ABI v1 `writeInput?`).

The `wasm_mem` tactic (`Silmaril.Wasm.Logic.Tactic.Defs`) discharges the bounds
and disjointness side conditions, which are linear arithmetic on addresses.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Core

open Silmaril.Wasm.Execution

theorem Region.Disjoint.symm {r q : Region} (h : r.Disjoint q) : q.Disjoint r := Or.symm h

theorem length_bytesAt {B : ByteArray} {r : Region} (h : r.InBounds B) :
    (bytesAt B r).length = r.len := by
  simp only [Region.InBounds, Region.stop] at h
  simp only [bytesAt, List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data]
  omega

/-- The `i`-th byte of a region, as an optional list element. -/
theorem getElem?_bytesAt (B : ByteArray) (r : Region) (i : Nat) :
    (bytesAt B r)[i]? = if i < r.len then B.data.toList[r.base + i]? else none := by
  simp only [bytesAt, List.getElem?_take, List.getElem?_drop]

/-! ## Little-endian encodings -/

theorem leNat_cons (b : UInt8) (l : List UInt8) : leNat (b :: l) = b.toNat + 256 * leNat l :=
  rfl

theorem pow_eight_succ (k : Nat) : 2 ^ (8 * (k + 1)) = 256 * 2 ^ (8 * k) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

/-- The bytes of `Memory.encodeLE n v` are the little-endian digits of `v`. -/
theorem toList_encodeLE (n v : Nat) :
    (Memory.encodeLE n v).data.toList = (List.range n).map fun k => UInt8.ofNat (v / 2 ^ (8 * k)) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [Memory.encodeLE, ByteArray.toList_data_append, ih, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    show UInt8.ofNat v :: _ = UInt8.ofNat (v / 2 ^ (8 * 0)) :: _
    congr 1
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    · apply List.map_congr_left
      intro k _
      simp only [Function.comp]
      rw [Nat.div_div_eq_div_mul, ← pow_eight_succ]

theorem leNat_encodeLE (n v : Nat) : leNat (Memory.encodeLE n v).data.toList = v % 256 ^ n := by
  have := Memory.decodeLE_encodeLE n v
  simp only [Memory.decodeLE, ← Array.foldr_toList] at this
  exact this

theorem u32le_eq (x : UInt32) : u32le x = (Memory.encodeLE 4 x.toNat).data.toList := by
  rw [toList_encodeLE, show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  rfl

theorem u64le_eq (x : UInt64) : u64le x = (Memory.encodeLE 8 x.toNat).data.toList := by
  rw [toList_encodeLE]
  rfl

theorem leNat_u32le (x : UInt32) : leNat (u32le x) = x.toNat := by
  rw [u32le_eq, leNat_encodeLE]
  exact Nat.mod_eq_of_lt x.toBitVec.isLt

theorem leNat_u64le (x : UInt64) : leNat (u64le x) = x.toNat := by
  rw [u64le_eq, leNat_encodeLE]
  exact Nat.mod_eq_of_lt x.toBitVec.isLt

theorem leNat_append (l₁ l₂ : List UInt8) :
    leNat (l₁ ++ l₂) = leNat l₁ + 2 ^ (8 * l₁.length) * leNat l₂ := by
  induction l₁ with
  | nil => simp [leNat]
  | cons b l ih =>
    rw [List.cons_append, leNat_cons, leNat_cons, ih, List.length_cons, pow_eight_succ]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem leNat_lt (l : List UInt8) : leNat l < 2 ^ (8 * l.length) := by
  induction l with
  | nil => simp [leNat]
  | cons b l ih =>
    rw [leNat_cons, List.length_cons, pow_eight_succ]
    have hb := b.toNat_lt
    omega

/-- `Memory.decodeLE` is `leNat` of the bytes. -/
theorem decodeLE_eq_leNat (b : ByteArray) : Memory.decodeLE b = leNat b.data.toList := by
  simp only [Memory.decodeLE, leNat, Array.foldr_toList]

/-! ## Loads and stores -/

/-- **An in-bounds load** is the little-endian value of the region. -/
theorem load_eq {B : ByteArray} {a n : Nat} (h : a + n ≤ B.size) :
    Memory.load B a n = some (BitVec.ofNat (8 * n) (leNat (bytesAt B ⟨a, n⟩))) := by
  simp only [Memory.load, Memory.readBytes, h, ↓reduceIte, Option.map_some, decodeLE_eq_leNat,
    ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    Nat.add_sub_cancel_left, bytesAt]

/-- An out-of-bounds load fails. -/
theorem load_eq_none {B : ByteArray} {a n : Nat} (h : B.size < a + n) :
    Memory.load B a n = none := by
  simp only [Memory.load, Memory.readBytes, Nat.not_le.mpr h, ↓reduceIte, Option.map_none]

theorem size_encodeLE (n v : Nat) : (Memory.encodeLE n v).size = n := by
  exact Memory.encodeLE_size n v

/-- **An in-bounds store.** -/
theorem store_eq {B : ByteArray} {a n : Nat} (w : BitVec (8 * n)) (h : a + n ≤ B.size) :
    Memory.store B a w = some (storeLE B a n w.toNat) := by
  simp only [Memory.store, Memory.writeBytes, storeLE, Memory.encodeLE_size, h, ↓reduceIte]

/-- A store does not change the size of memory. -/
theorem size_store {B B' : ByteArray} {a n : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B a w = some B') : B'.size = B.size := by
  exact Memory.writeBytes_size B _ B' a h

/-- **Read after write, same region.** -/
theorem load_store_same {B B' : ByteArray} {a n : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B a w = some B') : Memory.load B' a n = some w := by
  exact Memory.load_store B B' a n w h

/-- A successful host write, as a list splice. -/
theorem toList_writeBytes {B B' D : ByteArray} {p : Nat} (h : Memory.writeBytes B p D = some B') :
    p + D.size ≤ B.size ∧
      B'.data.toList = B.data.toList.take p ++ D.data.toList ++ B.data.toList.drop (p + D.size) := by
  obtain ⟨hb, rfl⟩ := (Memory.writeBytes_eq_some_iff B D B' p).mp h
  refine ⟨hb, ?_⟩
  simp only [ByteArray.toList_data_append, ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
  congr 1
  exact List.take_of_length_le
    (by simp only [List.length_drop, Array.length_toList, ByteArray.size_data]; omega)

/-- Reading a byte of a splice. -/
theorem getElem?_splice {L D : List UInt8} {p k : Nat} (hp : p + D.length ≤ L.length) :
    (L.take p ++ D ++ L.drop (p + D.length))[k]? =
      if p ≤ k ∧ k < p + D.length then D[k - p]? else L[k]? := by
  simp only [List.getElem?_append, List.length_append, List.length_take, List.getElem?_take,
    List.getElem?_drop]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- **Separation for host writes**: bytes of a region disjoint from the write are unchanged. -/
theorem bytesAt_writeBytes_disjoint {B B' D : ByteArray} {p : Nat} {r : Region}
    (h : Memory.writeBytes B p D = some B') (hd : Region.Disjoint ⟨p, D.size⟩ r) :
    bytesAt B' r = bytesAt B r := by
  obtain ⟨hb, hL⟩ := toList_writeBytes h
  have hp : p + D.data.toList.length ≤ B.data.toList.length := by
    simp only [Array.length_toList, ByteArray.size_data]; omega
  apply List.ext_getElem?
  intro i
  rw [getElem?_bytesAt, getElem?_bytesAt, hL,
    show D.size = D.data.toList.length from rfl, getElem?_splice hp]
  simp only [Region.Disjoint, Region.stop, Array.length_toList, ByteArray.size_data] at hd ⊢
  split_ifs <;> first | rfl | omega

/-- Inside the written range, the bytes are the written data's (helper form). -/
theorem bytesAt_writeBytes_inside' {B B' data : ByteArray} {p : Nat} {r : Region}
    (h : Memory.writeBytes B p data = some B') (hr : Region.Contains ⟨p, data.size⟩ r) :
    bytesAt B' r = bytesAt data ⟨r.base - p, r.len⟩ := by
  obtain ⟨hb, hL⟩ := toList_writeBytes h
  have hp : p + data.data.toList.length ≤ B.data.toList.length := by
    simp only [Array.length_toList, ByteArray.size_data]; omega
  apply List.ext_getElem?
  intro i
  rw [getElem?_bytesAt, getElem?_bytesAt, hL,
    show data.size = data.data.toList.length from rfl, getElem?_splice hp]
  dsimp only
  simp only [Region.Contains, Region.stop, Array.length_toList, ByteArray.size_data] at hr ⊢
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- **Separation**: a store leaves the bytes of a disjoint region unchanged. -/
theorem bytesAt_store_disjoint {B B' : ByteArray} {a n : Nat} {w : BitVec (8 * n)} {r : Region}
    (h : Memory.store B a w = some B') (hd : Region.Disjoint ⟨a, n⟩ r) :
    bytesAt B' r = bytesAt B r := by
  have hw : Memory.writeBytes B a (Memory.encodeLE n w.toNat) = some B' := h
  exact bytesAt_writeBytes_disjoint hw (by rw [Memory.encodeLE_size]; exact hd)

/-- **Separation for loads**: a load from a region disjoint from a store is unchanged. -/
theorem load_store_disjoint {B B' : ByteArray} {a n b m : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B a w = some B') (hd : Region.Disjoint ⟨a, n⟩ ⟨b, m⟩) :
    Memory.load B' b m = Memory.load B b m := by
  have hs := size_store h
  by_cases hb : b + m ≤ B.size
  · rw [load_eq (B := B') (by omega), load_eq hb, bytesAt_store_disjoint h hd]
  · rw [load_eq_none (B := B') (by omega), load_eq_none (B := B) (by omega)]

/-- The bytes of the region a store wrote. -/
theorem bytesAt_store_same {B B' : ByteArray} {a n : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B a w = some B') :
    bytesAt B' ⟨a, n⟩ = (Memory.encodeLE n w.toNat).data.toList := by
  have hw : Memory.writeBytes B a (Memory.encodeLE n w.toNat) = some B' := h
  rw [bytesAt_writeBytes_inside' (r := ⟨a, n⟩) hw
    (by simp only [Region.Contains, Region.stop, Memory.encodeLE_size]; omega)]
  simp only [bytesAt, Nat.sub_self, List.drop_zero]
  exact List.take_of_length_le
    (by simp only [Array.length_toList, ByteArray.size_data, Memory.encodeLE_size]; omega)

/-- The bytes of a region after the host wrote `data` at `p` (ABI v1 input):
inside the written range they are `data`'s. -/
theorem bytesAt_writeBytes_inside {B B' data : ByteArray} {p : Nat} {r : Region}
    (h : Memory.writeBytes B p data = some B') (hr : Region.Contains ⟨p, data.size⟩ r) :
    bytesAt B' r = bytesAt data ⟨r.base - p, r.len⟩ :=
  bytesAt_writeBytes_inside' h hr

/-- A `u32` stored at `a` reads back as its little-endian bytes. -/
theorem bytesAt_store_u32 {B B' : ByteArray} {a : Nat} {x : UInt32}
    (h : Memory.store B a (count := 4) (BitVec.ofNat 32 x.toNat) = some B') :
    bytesAt B' ⟨a, 4⟩ = u32le x := by
  rw [bytesAt_store_same h, u32le_eq]
  have e : (BitVec.ofNat 32 x.toNat).toNat = x.toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.toBitVec.isLt
  rw [e]

/-- The bytes after a store. -/
theorem getElem?_store {B B' : ByteArray} {p n : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B p w = some B') (j : Nat) :
    B'.data.toList[j]? = if p ≤ j ∧ j < p + n then
      (Memory.encodeLE n w.toNat).data.toList[j - p]? else B.data.toList[j]? := by
  obtain ⟨hb, heq⟩ := toList_writeBytes (D := Memory.encodeLE n w.toNat) h
  have hlen : (Memory.encodeLE n w.toNat).data.toList.length = n := by simp
  have hb' : p + (Memory.encodeLE n w.toNat).data.toList.length ≤ B.data.toList.length := by
    simpa using hb
  rw [heq, show (Memory.encodeLE n w.toNat).size = (Memory.encodeLE n w.toNat).data.toList.length
    by simp, getElem?_splice hb', hlen]

end Silmaril.Wasm.Logic.Core
