module

public import Silmaril.Prelude.Bytes.Write.Defs
public import Silmaril.Proofs.Prelude.Bytes.Basic
import Init.Omega

/-! Proofs for `Silmaril.Prelude.Bytes.Write.Thms`. The digit lemma and `write_spec` are
ported from `Silmaril.Proofs.Wasm.KernelEval.KBytesMem` (hiloopai/silmaril-lean#133, `kwrite`),
restated on `List UInt8`; the rest is new. -/

@[expose] public section

namespace Silmaril.Proofs.Prelude.Bytes

open Silmaril Silmaril.KBytes

/-! ## Digits -/

theorem unpack_add' (a b y : Nat) : unpack (a + b) y = unpack a y ++ unpack b (y / 256 ^ a) := by
  rw [unpack_add, unpack_mod]

theorem getElem?_unpack : ∀ (k v j : Nat),
    (unpack k v)[j]? = if j < k then some (UInt8.ofNat (v / 256 ^ j)) else none
  | 0, _, _ => by simp [unpack]
  | k + 1, v, 0 => by simp [unpack]
  | k + 1, v, j + 1 => by
    simp only [unpack, List.getElem?_cons_succ, getElem?_unpack k (v / 256) j,
      Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ j) 256]
    simp only [Nat.mul_comm 256 (256 ^ j)]
    split <;> split <;> first | rfl | omega

/-- The digit-wise leaf write. -/
theorem unpack_leafWrite (n x off w v : Nat) (h : off + w ≤ n) :
    unpack n (x % 256 ^ off + 256 ^ off * (v % 256 ^ w + 256 ^ w * (x / 256 ^ (off + w))))
      = (unpack n x).take off ++ unpack w v ++ (unpack n x).drop (off + w) := by
  have hpos : ∀ k, 0 < 256 ^ k := fun k => Nat.pow_pos (by decide)
  obtain ⟨r, rfl⟩ : ∃ r, n = off + w + r := ⟨n - (off + w), by omega⟩
  have hx : unpack (off + w + r) x =
      unpack off x ++ (unpack w (x / 256 ^ off) ++ unpack r (x / 256 ^ (off + w))) := by
    rw [Nat.add_assoc, unpack_add', unpack_add' w r, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have e1 : (unpack (off + w + r) x).take off = unpack off x := by
    rw [hx, List.take_left' (length_unpack _ _)]
  have e2 : (unpack (off + w + r) x).drop (off + w) = unpack r (x / 256 ^ (off + w)) := by
    rw [hx, ← List.append_assoc, List.drop_left' (by simp [length_unpack])]
  rw [e1, e2, Nat.add_assoc, unpack_add', unpack_add' w r]
  have hlt : x % 256 ^ off < 256 ^ off := Nat.mod_lt _ (hpos off)
  rw [Nat.add_mul_div_left _ _ (hpos off), Nat.div_eq_of_lt hlt, Nat.zero_add,
    Nat.add_mul_div_left _ _ (hpos w), Nat.div_eq_of_lt (Nat.mod_lt _ (hpos w)), Nat.zero_add]
  rw [← unpack_mod off (x % 256 ^ off + _), Nat.add_mul_mod_self_left, Nat.mod_mod,
    unpack_mod off, ← unpack_mod w (v % 256 ^ w + _), Nat.add_mul_mod_self_left, Nat.mod_mod,
    unpack_mod w v]
  simp

/-! ## Path-copying writes -/

theorem len_write : ∀ (t : KBytes) (off w v : Nat), (t.write off w v).len = t.len
  | .leaf _ _, _, _, _ => rfl
  | .node _ l r, off, w, v => by simp only [write]; split <;> (try split) <;> rfl

theorem write_spec : ∀ (t : KBytes) (off w v : Nat), t.wf = true → off + w ≤ t.len →
    (t.write off w v).wf = true ∧ (t.write off w v).toList = splice t.toList off w v
  | .leaf n x, off, w, v, _, h => ⟨rfl, unpack_leafWrite n x off w v h⟩
  | .node n l r, off, w, v, hw, h => by
    obtain ⟨hn, hl, hr⟩ := wf_node.1 hw
    have hL := length_toList l hl
    have hR := length_toList r hr
    simp only [len] at h
    simp only [write, splice]
    split
    · rename_i c
      obtain ⟨w1, t1⟩ := write_spec l off w v hl c
      refine ⟨wf_node.2 ⟨by rw [len_write]; exact hn, w1, hr⟩, ?_⟩
      simp only [toList, t1, splice,
        List.take_append_of_le_length (show off ≤ l.toList.length by omega),
        List.drop_append_of_le_length (show off + w ≤ l.toList.length by omega), List.append_assoc]
    · split
      · rename_i c1 c2
        obtain ⟨w1, t1⟩ := write_spec r (off - l.len) w v hr (by omega)
        refine ⟨wf_node.2 ⟨by rw [len_write]; exact hn, hl, w1⟩, ?_⟩
        simp only [toList, t1, splice, List.take_append, List.drop_append, hL,
          List.take_of_length_le (show l.toList.length ≤ off by omega),
          List.drop_eq_nil_of_le (show l.toList.length ≤ off + w by omega),
          List.nil_append, List.append_assoc, show off + w - l.len = off - l.len + w by omega]
      · rename_i c1 c2
        obtain ⟨w1, t1⟩ := write_spec l off (l.len - off) v hl (by omega)
        obtain ⟨w2, t2⟩ := write_spec r 0 (w - (l.len - off)) (v / 256 ^ (l.len - off)) hr
          (by omega)
        refine ⟨wf_node.2 ⟨by rw [len_write, len_write]; exact hn, w1, w2⟩, ?_⟩
        simp only [toList, t1, t2, splice, List.take_zero, List.nil_append,
          List.drop_of_length_le (show l.toList.length ≤ off + (l.len - off) by omega),
          List.append_nil, List.take_append_of_le_length (show off ≤ l.toList.length by omega),
          List.drop_append, List.drop_eq_nil_of_le (show l.toList.length ≤ off + w by omega), hL,
          Nat.zero_add, show off + w - l.len = w - (l.len - off) by omega, List.append_assoc]
        rw [← List.append_assoc (unpack _ v), ← unpack_add',
          show l.len - off + (w - (l.len - off)) = w by omega]

theorem leafBound_write (c : Nat) : ∀ (t : KBytes) (off w v : Nat),
    leafBound c (t.write off w v) = leafBound c t
  | .leaf _ _, _, _, _ => rfl
  | .node _ l r, off, w, v => by
    simp only [write]
    split
    · simp only [leafBound, leafBound_write c l]
    · split
      · simp only [leafBound, leafBound_write c r]
      · simp only [leafBound, leafBound_write c l, leafBound_write c r]

theorem leafWrite_lt {n x off w v : Nat} (hx : x < 256 ^ n) (h : off + w ≤ n) :
    x % 256 ^ off + 256 ^ off * (v % 256 ^ w + 256 ^ w * (x / 256 ^ (off + w))) < 256 ^ n := by
  have hpos : ∀ k, 0 < 256 ^ k := fun k => Nat.pow_pos (by decide)
  obtain ⟨r, rfl⟩ : ∃ r, n = off + w + r := ⟨n - (off + w), by omega⟩
  have hq : x / 256 ^ (off + w) < 256 ^ r := by
    rw [Nat.div_lt_iff_lt_mul (hpos _), ← Nat.pow_add, Nat.add_comm r]; exact hx
  -- `a < A` and `b < B` give `a + A * b < A * B`.
  have key : ∀ {a b A B : Nat}, a < A → b < B → a + A * b < A * B := by
    intro a b A B ha hb
    have : A * b + A ≤ A * B := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hb
    omega
  have e : 256 ^ (off + w + r) = 256 ^ off * (256 ^ w * 256 ^ r) := by
    rw [Nat.pow_add, Nat.pow_add, Nat.mul_assoc]
  rw [e]
  exact key (Nat.mod_lt _ (hpos off)) (key (Nat.mod_lt _ (hpos w)) hq)

theorem normal_write : ∀ (t : KBytes) (off w v : Nat), t.wf = true → off + w ≤ t.len →
    normal t = true → normal (t.write off w v) = true
  | .leaf n x, off, w, v, _, h, hn => by
    simp only [normal, decide_eq_true_eq, len] at hn h
    simp only [write, normal, decide_eq_true_eq]
    exact leafWrite_lt hn h
  | .node n l r, off, w, v, hw, h, hnm => by
    obtain ⟨hn, hl, hr⟩ := wf_node.1 hw
    simp only [len] at h
    simp only [normal, Bool.and_eq_true] at hnm
    simp only [write]
    split
    · simp only [normal, Bool.and_eq_true]
      exact ⟨normal_write l off w v hl (by omega) hnm.1, hnm.2⟩
    · split
      · simp only [normal, Bool.and_eq_true]
        exact ⟨hnm.1, normal_write r _ w v hr (by omega) hnm.2⟩
      · simp only [normal, Bool.and_eq_true]
        exact ⟨normal_write l _ _ v hl (by omega) hnm.1,
          normal_write r _ _ _ hr (by omega) hnm.2⟩

/-! ## Rope writes -/

theorem ropeWrite_spec (t : KBytes) (off w v : Nat) (ht : t.wf = true) (h : off + w ≤ t.len) :
    (t.ropeWrite off w v).wf = true ∧ (t.ropeWrite off w v).toList = splice t.toList off w v := by
  have hL := length_toList t ht
  have s1 := (slice_spec t 0 off ht (by omega)).2
  have s2 := (slice_spec t (off + w) (t.len - (off + w)) ht (by omega)).2
  refine ⟨wf_append (wf_append (slice_spec t 0 off ht (by omega)).1 rfl)
    (slice_spec t _ _ ht (by omega)).1, ?_⟩
  simp only [ropeWrite, toList_append, s1, s2, List.drop_zero, splice]
  rw [List.take_of_length_le (l := List.drop (off + w) t.toList) (by simp [hL])]
  show _ ++ unpack w (v % 256 ^ w) ++ _ = _
  rw [unpack_mod]

theorem len_ropeWrite (t : KBytes) (off w v : Nat) (h : off + w ≤ t.len) :
    (t.ropeWrite off w v).len = t.len := by
  show (t.slice 0 off).len + w + (t.slice (off + w) (t.len - (off + w))).len = t.len
  rw [len_slice, len_slice]
  omega

/-! ## Byte lists -/

theorem length_splice (bs : List UInt8) (off w v : Nat) (h : off + w ≤ bs.length) :
    (splice bs off w v).length = bs.length := by
  simp only [splice, List.length_append, List.length_take, List.length_drop, length_unpack]
  omega

theorem getElem?_splice (bs : List UInt8) (off w v i : Nat) (h : off + w ≤ bs.length) :
    (splice bs off w v)[i]? =
      if off ≤ i ∧ i < off + w then some (UInt8.ofNat (v / 256 ^ (i - off))) else bs[i]? := by
  simp only [splice, List.append_assoc]
  rw [List.getElem?_append]
  simp only [List.length_take, Nat.min_eq_left (show off ≤ bs.length by omega)]
  split
  · rename_i hi
    rw [List.getElem?_take, ite_eq_left hi, ite_eq_right (by omega)]
  · rw [List.getElem?_append, length_unpack]
    split
    · rename_i h1 h2
      rw [getElem?_unpack, ite_eq_left h2, ite_eq_left (by omega)]
    · rename_i h1 h2
      rw [List.getElem?_drop, ite_eq_right (by omega)]
      congr 1; omega

/-- A window of a list depends only on the positions in it. -/
theorem take_drop_congr {L₁ L₂ : List UInt8} {a k : Nat}
    (h : ∀ i, a ≤ i → i < a + k → L₁[i]? = L₂[i]?) :
    (L₁.drop a).take k = (L₂.drop a).take k := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop]
  split
  · exact h _ (by omega) (by omega)
  · rfl

theorem readLE_congr {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true)
    (h : a.toList = b.toList) (off w : Nat) : a.readLE off w = b.readLE off w := by
  rw [readLE_eq a ha, readLE_eq b hb, h]

/-! ## Consequences of the byte-list specification

Stated for any `t'` whose bytes are `splice t.toList off w v`, so they hold for both writes. -/

section
variable {t t' : KBytes} {off w v : Nat}

theorem get?_of_splice (ht : t.wf = true) (ht' : t'.wf = true)
    (hs : t'.toList = splice t.toList off w v) (h : off + w ≤ t.len) (i : Nat) :
    t'.get? i = if off ≤ i ∧ i < off + w then some (UInt8.ofNat (v / 256 ^ (i - off)))
      else t.get? i := by
  rw [get?_eq t' ht', get?_eq t ht, hs, getElem?_splice _ _ _ _ _ (by rw [length_toList t ht]; exact h)]

theorem readLE_self_of_splice (ht : t.wf = true) (ht' : t'.wf = true)
    (hs : t'.toList = splice t.toList off w v) (h : off + w ≤ t.len) :
    t'.readLE off w = some (v % 256 ^ w) := by
  have hL := length_toList t ht
  rw [readLE_eq t' ht', hs, length_splice _ _ _ _ (by omega), ite_eq_left (by omega)]
  simp only [splice, List.append_assoc]
  rw [List.drop_append_of_le_length (by simp; omega), List.drop_eq_nil_of_le (by simp; omega),
    List.nil_append, List.take_append_of_le_length (by simp [length_unpack]),
    List.take_of_length_le (by simp [length_unpack]), leVal_unpack]

theorem readLE_disjoint_of_splice (ht : t.wf = true) (ht' : t'.wf = true)
    (hs : t'.toList = splice t.toList off w v) (h : off + w ≤ t.len) {a k : Nat}
    (hd : a + k ≤ off ∨ off + w ≤ a) : t'.readLE a k = t.readLE a k := by
  have hL := length_toList t ht
  rw [readLE_eq t' ht', readLE_eq t ht, hs, length_splice _ _ _ _ (by omega)]
  congr 1
  rw [take_drop_congr (L₂ := t.toList)]
  intro i h1 h2
  rw [getElem?_splice _ _ _ _ _ (by omega), ite_eq_right (by omega)]

end

theorem get?_write (t : KBytes) (ht : t.wf = true) {off w : Nat} (v : Nat)
    (h : off + w ≤ t.len) (i : Nat) :
    (t.write off w v).get? i = if off ≤ i ∧ i < off + w then
      some (UInt8.ofNat (v / 256 ^ (i - off))) else t.get? i :=
  get?_of_splice ht (write_spec t off w v ht h).1 (write_spec t off w v ht h).2 h i

/-- Disjoint writes commute (as bytes). -/
theorem toList_write_comm (t : KBytes) (ht : t.wf = true) {a k b m : Nat} (u v : Nat)
    (ha : a + k ≤ t.len) (hb : b + m ≤ t.len) (hd : a + k ≤ b ∨ b + m ≤ a) :
    ((t.write a k u).write b m v).toList = ((t.write b m v).write a k u).toList := by
  obtain ⟨w1, _⟩ := write_spec t a k u ht ha
  obtain ⟨w2, _⟩ := write_spec t b m v ht hb
  have l1 := len_write t a k u
  have l2 := len_write t b m v
  obtain ⟨w3, _⟩ := write_spec _ b m v w1 (by omega)
  obtain ⟨w4, _⟩ := write_spec _ a k u w2 (by omega)
  apply List.ext_getElem?
  intro i
  rw [← get?_eq _ w3, ← get?_eq _ w4, get?_write _ w1 v (by omega), get?_write _ w2 u (by omega),
    get?_write t ht u ha, get?_write t ht v hb]
  by_cases h1 : a ≤ i ∧ i < a + k <;> by_cases h2 : b ≤ i ∧ i < b + m <;> simp [h1, h2] <;> omega

/-! ## Slices -/

theorem readLE_slice (t : KBytes) (ht : t.wf = true) {off w : Nat} (h : off + w ≤ t.len)
    (o k : Nat) :
    (t.slice off w).readLE o k = if o + k ≤ w then t.readLE (off + o) k else none := by
  obtain ⟨hs, hl⟩ := slice_spec t off w ht h
  have hL := length_toList t ht
  rw [readLE_eq _ hs, readLE_eq t ht, hl]
  simp only [List.length_take, List.length_drop, hL, Nat.min_eq_left (show w ≤ t.len - off by omega)]
  split
  · rename_i hk
    rw [ite_eq_left (by omega), List.drop_take, List.take_take, List.drop_drop,
      Nat.min_eq_left (by omega)]
  · rfl

/-! ## Zeros -/

theorem unpack_zero : ∀ k, unpack k 0 = List.replicate k 0
  | 0 => rfl
  | k + 1 => by simp [unpack, unpack_zero k, List.replicate_succ]

theorem chunksBytes_zeros (c : Nat) : ∀ (k n : Nat), n ≤ c * k →
    chunksBytes c n (List.replicate k 0) = List.replicate n 0
  | 0, n, h => by simp at h; subst h; rfl
  | k + 1, n, h => by
    simp only [List.replicate_succ, chunksBytes, unpack_zero,
      chunksBytes_zeros c k (n - c) (by rw [Nat.mul_succ] at h; omega),
      List.replicate_append_replicate]
    congr 1; omega

theorem toList_zerosCanon (c n : Nat) (hc : 0 < c) :
    (zerosCanon c n).toList = List.replicate n 0 := by
  rw [zerosCanon, (ofChunks_spec c n _).2, chunksBytes_zeros]
  have := Nat.div_add_mod (n + c - 1) c
  have := Nat.mod_lt (n + c - 1) hc
  rw [Nat.mul_comm]
  -- `n ≤ c * ⌈n / c⌉`
  have h2 : (n + c - 1) / c * c + (n + c - 1) % c = n + c - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  omega

end Silmaril.Proofs.Prelude.Bytes
