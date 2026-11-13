module

public import Silmaril.Wasm.KernelEval.KBytesMem
public import Silmaril.Prelude.Bytes.Thms
public import Silmaril.Proofs.Wasm.KernelEval.Memories

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: `KBytes` as Wasm memory, proofs

Statements in `Silmaril.Wasm.KernelEval.KBytesMemThms`.
-/

namespace Silmaril.Proofs.Wasm.KernelEval

open Silmaril Silmaril.Wasm.KernelEval

/-! ## Digits -/

theorem leVal_eq_pack : ∀ L : List UInt8, KBytes.leVal L = ListMem.pack (L.map UInt8.toBitVec)
  | [] => rfl
  | b :: L => by simp [KBytes.leVal, ListMem.pack, leVal_eq_pack L]

theorem unpack_map : ∀ (k v : Nat), (KBytes.unpack k v).map UInt8.toBitVec = ListMem.encode k v
  | 0, _ => rfl
  | k + 1, v => by
    simp [KBytes.unpack, ListMem.encode, unpack_map k (v / 256), UInt8.toBitVec_ofNat']

theorem unpack_add : ∀ (a b y : Nat),
    KBytes.unpack (a + b) y = KBytes.unpack a y ++ KBytes.unpack b (y / 256 ^ a)
  | 0, b, y => by simp [KBytes.unpack]
  | a + 1, b, y => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [KBytes.unpack, unpack_add a b (y / 256), List.cons_append, Nat.div_div_eq_div_mul,
      Nat.pow_succ, Nat.mul_comm (256 ^ a) 256]

theorem unpack_mod : ∀ (a y : Nat), KBytes.unpack a y = KBytes.unpack a (y % 256 ^ a)
  | 0, _ => rfl
  | a + 1, y => by
    simp only [KBytes.unpack]
    rw [show 256 ^ (a + 1) = 256 * 256 ^ a by rw [Nat.pow_succ, Nat.mul_comm],
      Nat.mod_mul_right_div_self, ← unpack_mod a (y / 256)]
    congr 1
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp [UInt8.toBitVec_ofNat', Nat.mod_mul_right_mod]

/-- The digit-wise leaf write. -/
theorem unpack_leafWrite (n x off w v : Nat) (h : off + w ≤ n) :
    KBytes.unpack n (x % 256 ^ off + 256 ^ off * (v % 256 ^ w + 256 ^ w * (x / 256 ^ (off + w))))
      = (KBytes.unpack n x).take off ++ KBytes.unpack w v ++ (KBytes.unpack n x).drop (off + w) := by
  have hpos : ∀ k, 0 < 256 ^ k := fun k => Nat.pow_pos (by decide)
  obtain ⟨r, rfl⟩ : ∃ r, n = off + w + r := ⟨n - (off + w), by omega⟩
  have hx : KBytes.unpack (off + w + r) x =
      KBytes.unpack off x ++ (KBytes.unpack w (x / 256 ^ off) ++
        KBytes.unpack r (x / 256 ^ (off + w))) := by
    rw [Nat.add_assoc, unpack_add, unpack_add w r, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have e1 : (KBytes.unpack (off + w + r) x).take off = KBytes.unpack off x := by
    rw [hx, List.take_left' (KBytes.length_unpack _ _)]
  have e2 : (KBytes.unpack (off + w + r) x).drop (off + w) =
      KBytes.unpack r (x / 256 ^ (off + w)) := by
    rw [hx, ← List.append_assoc, List.drop_left' (by simp [KBytes.length_unpack])]
  rw [e1, e2, Nat.add_assoc, unpack_add, unpack_add w r]
  have hlt : x % 256 ^ off < 256 ^ off := Nat.mod_lt _ (hpos off)
  rw [Nat.add_mul_div_left _ _ (hpos off), Nat.div_eq_of_lt hlt, Nat.zero_add,
    Nat.add_mul_div_left _ _ (hpos w), Nat.div_eq_of_lt (Nat.mod_lt _ (hpos w)), Nat.zero_add]
  rw [unpack_mod off (x % 256 ^ off + _), Nat.add_mul_mod_self_left, Nat.mod_mod,
    ← unpack_mod off, unpack_mod w (v % 256 ^ w + _), Nat.add_mul_mod_self_left, Nat.mod_mod,
    ← unpack_mod w v]
  simp

/-! ## Path-copying writes -/

theorem len_kwrite : ∀ (t : KBytes) (off w v : Nat), (kwrite t off w v).len = t.len
  | .leaf _ _, _, _, _ => rfl
  | .node _ l r, off, w, v => by simp only [kwrite]; split <;> (try split) <;> rfl

theorem kwrite_spec : ∀ (t : KBytes) (off w v : Nat), t.wf = true → off + w ≤ t.len →
    (kwrite t off w v).wf = true ∧ (kwrite t off w v).toList =
      t.toList.take off ++ KBytes.unpack w v ++ t.toList.drop (off + w)
  | .leaf n x, off, w, v, _, h => ⟨rfl, unpack_leafWrite n x off w v h⟩
  | .node n l r, off, w, v, hw, h => by
    simp only [KBytes.wf, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨hn, hl⟩, hr⟩ := hw
    have hL := KBytes.length_toList l hl
    have hR := KBytes.length_toList r hr
    simp only [KBytes.len] at h
    simp only [kwrite]
    split
    · rename_i c
      obtain ⟨w1, t1⟩ := kwrite_spec l off w v hl c
      refine ⟨by simp [KBytes.wf, len_kwrite, hn, w1, hr], ?_⟩
      simp only [KBytes.toList, t1, List.take_append_of_le_length (show off ≤ l.toList.length by omega),
        List.drop_append_of_le_length (show off + w ≤ l.toList.length by omega), List.append_assoc]
    · split
      · rename_i c1 c2
        obtain ⟨w1, t1⟩ := kwrite_spec r (off - l.len) w v hr (by omega)
        refine ⟨by simp [KBytes.wf, len_kwrite, hn, w1, hl], ?_⟩
        simp only [KBytes.toList, t1, List.take_append, List.drop_append, hL,
          List.take_of_length_le (show l.toList.length ≤ off by omega),
          List.drop_eq_nil_of_le (show l.toList.length ≤ off + w by omega),
          List.nil_append, List.append_assoc, show off + w - l.len = off - l.len + w by omega]
      · rename_i c1 c2
        obtain ⟨w1, t1⟩ := kwrite_spec l off (l.len - off) v hl (by omega)
        obtain ⟨w2, t2⟩ := kwrite_spec r 0 (w - (l.len - off)) (v / 256 ^ (l.len - off)) hr
          (by omega)
        refine ⟨by simp [KBytes.wf, len_kwrite, hn, w1, w2], ?_⟩
        simp only [KBytes.toList, t1, t2, List.take_zero, List.nil_append,
          List.drop_of_length_le (show l.toList.length ≤ off + (l.len - off) by omega),
          List.append_nil, List.take_append_of_le_length (show off ≤ l.toList.length by omega),
          List.drop_append, List.drop_eq_nil_of_le (show l.toList.length ≤ off + w by omega), hL,
          Nat.zero_add,
          show off + w - l.len = w - (l.len - off) by omega, List.append_assoc]
        rw [← List.append_assoc (KBytes.unpack _ v), ← unpack_add,
          show l.len - off + (w - (l.len - off)) = w by omega]

/-! ## Simulations -/

theorem kbytes_load (t : KBytes) (ht : t.wf = true) (a k : Nat) :
    MemOps.load (kToListMem t) a k = t.readLE a k := by
  rw [KBytes.readLE_eq t ht]
  simp only [MemOps.load, kToListMem, List.length_map, leVal_eq_pack, List.map_take,
    List.map_drop]

theorem memSimOn_kPath : MemSimOn (fun m : KPath => m.t.wf = true) (fun m => kToListMem m.t) where
  load m hm a k := kbytes_load m.t hm a k
  store m hm a k v := by
    have hL := KBytes.length_toList m.t hm
    simp only [MemOps.store, kToListMem, List.length_map, hL]
    split
    · rename_i h
      simp only [Option.map_some,
        (kwrite_spec m.t a k v hm h).2, List.map_append, List.map_take, List.map_drop,
        unpack_map]
    · rfl
  store_inv m hm a k v m' hs := by
    simp only [MemOps.store] at hs
    split at hs
    · cases hs; exact (kwrite_spec m.t a k v hm (by assumption)).1
    · cases hs

theorem memSimOn_kRope : MemSimOn (fun m : KRope => m.t.wf = true) (fun m => kToListMem m.t) where
  load m hm a k := kbytes_load m.t hm a k
  store m hm a k v := by
    have hL := KBytes.length_toList m.t hm
    simp only [MemOps.store, kToListMem, List.length_map, hL]
    split
    · rename_i h
      have s1 := KBytes.toList_slice m.t 0 a hm (by omega)
      have s2 := KBytes.toList_slice m.t (a + k) (m.t.len - (a + k)) hm (by omega)
      have s3 : (KBytes.leaf k (v % 256 ^ k)).toList = KBytes.unpack k (v % 256 ^ k) := rfl
      simp only [Option.map_some, Option.some.injEq, ListMem.mk.injEq, KBytes.toList_append,
        s1, s2, s3, List.drop_zero, List.map_append, List.map_take, List.map_drop, unpack_map,
        encode_mod]
      rw [List.take_of_length_le (l := List.drop (a + k) (List.map UInt8.toBitVec m.t.toList))
        (by simp [hL])]
    · rfl
  store_inv m hm a k v m' hs := by
    simp only [MemOps.store] at hs
    split at hs
    · cases hs
      exact KBytes.wf_append (KBytes.wf_append (KBytes.wf_slice _ _ _ hm (by omega)) rfl)
        (KBytes.wf_slice _ _ _ hm (by omega))
    · cases hs

/-! ## Zero memories -/

theorem unpack_zero : ∀ k, KBytes.unpack k 0 = List.replicate k 0
  | 0 => rfl
  | k + 1 => by simp [KBytes.unpack, unpack_zero k, List.replicate_succ]

theorem chunksBytes_zeros (c : Nat) : ∀ (k n : Nat), n ≤ c * k →
    KBytes.chunksBytes c n (List.replicate k 0) = List.replicate n 0
  | 0, n, h => by simp at h; subst h; rfl
  | k + 1, n, h => by
    simp only [List.replicate_succ, KBytes.chunksBytes, unpack_zero,
      chunksBytes_zeros c k (n - c) (by rw [Nat.mul_succ] at h; omega), List.replicate_append_replicate]
    congr 1; omega

theorem wf_kzeros (n : Nat) : (kzeros n).wf = true := KBytes.wf_ofChunks _ _ _

theorem kzeros_toListMem (n : Nat) : kToListMem (kzeros n) = ⟨List.replicate n 0⟩ := by
  simp only [kToListMem, kzeros, KBytes.toList_ofChunks, ListMem.mk.injEq]
  rw [chunksBytes_zeros _ _ _ (by omega)]
  simp

end Silmaril.Proofs.Wasm.KernelEval
