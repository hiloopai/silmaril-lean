module

public import Silmaril.Prelude.Bytes.Defs
public import Silmaril.Proofs.Prelude.Bytes.Digits
import Init.Omega

/-! Proofs for `Silmaril.Prelude.Bytes.Thms`: the operations on kernel bytes against `toList`. -/

@[expose] public section

namespace Silmaril.Proofs.Prelude.Bytes

open Silmaril Silmaril.KBytes

/-! ## Lengths -/

theorem wf_node {n : Nat} {l r : KBytes} :
    (node n l r).wf = true ↔ n = l.len + r.len ∧ l.wf = true ∧ r.wf = true := by
  simp [wf, Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem length_toList : ∀ t : KBytes, t.wf = true → t.toList.length = t.len
  | leaf n v, _ => length_unpack n v
  | node n l r, h => by
    obtain ⟨hn, hl, hr⟩ := wf_node.1 h
    simp [toList, len, length_toList l hl, length_toList r hr, hn]

/-! ## Reads -/

theorem take_drop_append {l r : List UInt8} {off w : Nat} :
    ((l ++ r).drop off).take w =
      if off + w ≤ l.length then (l.drop off).take w
      else if l.length ≤ off then (r.drop (off - l.length)).take w
      else l.drop off ++ (r.drop 0).take (w - (l.length - off)) := by
  split
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · split
    · rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
    · rw [List.drop_append_of_le_length (by omega), List.take_append, List.take_of_length_le
        (by simp; omega)]
      simp only [List.length_drop, List.drop_zero]

theorem read_eq : ∀ (t : KBytes) (off w : Nat), t.wf = true → off + w ≤ t.len →
    t.read off w = leVal ((t.toList.drop off).take w)
  | leaf n v, off, w, _, h => by
    simp only [len] at h
    simp only [KBytes.read, toList, drop_unpack, take_unpack, leVal_unpack, Nat.shiftRight_eq_div_pow,
      pow256, Nat.min_eq_left (show w ≤ n - off by omega)]
  | node n l r, off, w, hw, h => by
    obtain ⟨hn, hl, hr⟩ := wf_node.1 hw
    simp only [len] at h
    have hll := length_toList l hl
    have hrl := length_toList r hr
    simp only [KBytes.read, toList, take_drop_append, hll]
    split
    · exact read_eq l off w hl (by omega)
    · split
      · exact read_eq r _ w hr (by omega)
      · rename_i h1 h2
        rw [read_eq l off _ hl (by omega), read_eq r 0 _ hr (by omega), leVal_append,
          Nat.shiftLeft_eq, pow256, List.take_of_length_le (by simp; omega)]
        simp only [List.length_drop, hll]
        rw [Nat.mul_comm]

theorem readLE_eq (t : KBytes) (hw : t.wf = true) (off w : Nat) :
    t.readLE off w =
      if off + w ≤ t.toList.length then some (leVal ((t.toList.drop off).take w)) else none := by
  simp only [readLE, length_toList t hw]
  split
  · rw [read_eq t off w hw (by omega)]
  · rfl

theorem get?_eq (t : KBytes) (hw : t.wf = true) (i : Nat) : t.get? i = t.toList[i]? := by
  simp only [get?, byte]
  split
  · rename_i hi
    rw [read_eq t i 1 hw (by omega)]
    have hl := length_toList t hw
    rw [List.getElem?_eq_getElem (by omega), ← List.getElem_cons_drop (h := by omega)]
    simp only [List.take_succ_cons, List.take_zero, leVal]
    simp
  · rename_i hi
    rw [List.getElem?_eq_none (by rw [length_toList t hw]; omega)]

/-! ## Ropes -/

theorem toList_append (a b : KBytes) : (a ++ b).toList = a.toList ++ b.toList := rfl

theorem wf_append {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) : (a ++ b).wf = true :=
  wf_node.2 ⟨rfl, ha, hb⟩

theorem len_slice : ∀ (t : KBytes) (off w : Nat), (t.slice off w).len = w
  | leaf _ _, _, _ => rfl
  | node _ l r, off, w => by
    simp only [slice]
    split
    · exact len_slice l off w
    · split
      · exact len_slice r _ w
      · rfl

theorem slice_spec : ∀ (t : KBytes) (off w : Nat), t.wf = true → off + w ≤ t.len →
    (t.slice off w).wf = true ∧ (t.slice off w).toList = (t.toList.drop off).take w
  | leaf n v, off, w, _, h => by
    simp only [len] at h
    refine ⟨rfl, ?_⟩
    simp only [slice, toList, drop_unpack, take_unpack, Nat.shiftRight_eq_div_pow, pow256,
      unpack_mod, Nat.min_eq_left (show w ≤ n - off by omega)]
  | node n l r, off, w, hw, h => by
    obtain ⟨hn, hl, hr⟩ := wf_node.1 hw
    simp only [len] at h
    have hll := length_toList l hl
    simp only [slice, toList, take_drop_append, hll]
    split
    · exact slice_spec l off w hl (by omega)
    · split
      · exact slice_spec r _ w hr (by omega)
      · obtain ⟨h1, h2⟩ := slice_spec l off (l.len - off) hl (by omega)
        obtain ⟨h3, h4⟩ := slice_spec r 0 (w - (l.len - off)) hr (by omega)
        refine ⟨wf_node.2 ⟨by rw [len_slice, len_slice]; omega, h1, h3⟩, ?_⟩
        rw [toList, h2, h4, List.take_of_length_le (by simp; omega)]

/-! ## Canonical form -/

theorem len_canonAux (t : KBytes) (c : Nat) : ∀ fuel off n, (t.canonAux c fuel off n).len = n
  | 0, _, _ => rfl
  | fuel + 1, off, n => by
    simp only [canonAux]
    split <;> rfl

theorem leftLeaves_lt {k : Nat} (hk : 2 ≤ k) : leftLeaves k ≤ k - 1 :=
  Nat.log2_self_le (by omega)

theorem unpack_read (t : KBytes) (ht : t.wf = true) {off n : Nat} (h : off + n ≤ t.len) :
    unpack n (t.read off n) = (t.toList.drop off).take n := by
  rw [read_eq t off n ht h]
  have hl : ((t.toList.drop off).take n).length = n := by
    simp [length_toList t ht]; omega
  generalize (t.toList.drop off).take n = xs at hl ⊢
  subst hl
  exact unpack_leVal xs

theorem leftLeaves_mul_le {n c : Nat} (hc : ¬n ≤ c) : leftLeaves ((n + c - 1) / c) * c < n := by
  rcases Nat.eq_zero_or_pos c with h0 | hcpos
  · subst h0; simp; omega
  have hk : 2 ≤ (n + c - 1) / c := by
    apply (Nat.le_div_iff_mul_le hcpos).2; omega
  have := leftLeaves_lt hk
  have h2 : ((n + c - 1) / c - 1) * c < n := by
    rw [Nat.sub_mul, Nat.one_mul]
    have := Nat.div_mul_le_self (n + c - 1) c
    omega
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right c this) h2

theorem canonAux_spec (t : KBytes) (c : Nat) (ht : t.wf = true) : ∀ fuel off n,
    off + n ≤ t.len →
    (t.canonAux c fuel off n).wf = true ∧
      (t.canonAux c fuel off n).toList = (t.toList.drop off).take n
  | 0, off, n, h => ⟨rfl, unpack_read t ht h⟩
  | fuel + 1, off, n, h => by
    simp only [canonAux]
    split
    · exact ⟨rfl, unpack_read t ht h⟩
    · rename_i hc
      have hp := leftLeaves_mul_le hc
      generalize leftLeaves ((n + c - 1) / c) * c = p at hp ⊢
      obtain ⟨h1, h2⟩ := canonAux_spec t c ht fuel off p (by omega)
      obtain ⟨h3, h4⟩ := canonAux_spec t c ht fuel (off + p) (n - p) (by omega)
      refine ⟨wf_node.2 ⟨by rw [len_canonAux, len_canonAux]; omega, h1, h3⟩, ?_⟩
      simp only [toList, h2, h4]
      have : n = p + (n - p) := by omega
      conv => rhs; rw [this, List.take_add, List.drop_drop]

theorem canon_spec (c : Nat) (t : KBytes) (ht : t.wf = true) :
    (t.canon c).wf = true ∧ (t.canon c).toList = t.toList := by
  obtain ⟨h1, h2⟩ := canonAux_spec t c ht 64 0 t.len (by omega)
  refine ⟨h1, ?_⟩
  rw [canon, h2, List.drop_zero, List.take_of_length_le (by rw [length_toList t ht]; omega)]

/-! ## Equality -/

theorem toList_eq_of_beq : ∀ a b : KBytes, a.beq b = true → a.toList = b.toList
  | leaf n v, leaf m u, h => by
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]
  | node _ a b, node _ c d, h => by
    simp only [beq, Bool.and_eq_true] at h
    simp only [toList, toList_eq_of_beq a c h.1.2, toList_eq_of_beq b d h.2]
  | leaf .., node .., h => by simp [beq] at h
  | node .., leaf .., h => by simp [beq] at h

theorem sameBytes_go (w : Nat) (a b : KBytes) (ha : a.wf = true) (hb : b.wf = true)
    (hlen : a.len = b.len) : ∀ fuel off, sameBytes.go w a b a.len off fuel = true →
      (a.toList.drop off) = (b.toList.drop off)
  | 0, off, h => by
    simp only [sameBytes.go, decide_eq_true_eq] at h
    rw [List.drop_eq_nil_of_le (by rw [length_toList a ha]; omega),
      List.drop_eq_nil_of_le (by rw [length_toList b hb]; omega)]
  | fuel + 1, off, h => by
    simp only [sameBytes.go] at h
    split at h
    · rw [List.drop_eq_nil_of_le (by rw [length_toList a ha]; omega),
        List.drop_eq_nil_of_le (by rw [length_toList b hb]; omega)]
    · rename_i hoff
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have hw := h.1
      rw [read_eq a off _ ha (by omega), read_eq b off _ hb (by omega)] at hw
      have hwin := leVal_inj (by simp [length_toList a ha, length_toList b hb, hlen]) hw
      have hrest := sameBytes_go w a b ha hb hlen fuel (off + w) h.2
      rw [← List.take_append_drop (min w (a.len - off)) (a.toList.drop off),
        ← List.take_append_drop (min w (a.len - off)) (b.toList.drop off), hwin,
        List.drop_drop, List.drop_drop]
      congr 1
      rcases Nat.lt_or_ge w (a.len - off) with hlt | hge
      · rw [Nat.min_eq_left (by omega)]; exact hrest
      · rw [Nat.min_eq_right (by omega),
          List.drop_eq_nil_of_le (by rw [length_toList a ha]; omega),
          List.drop_eq_nil_of_le (by rw [length_toList b hb]; omega)]

theorem toList_eq_of_sameBytes (w : Nat) (a b : KBytes) (ha : a.wf = true) (hb : b.wf = true)
    (h : a.sameBytes w b = true) : a.toList = b.toList := by
  simp only [sameBytes, Bool.and_eq_true, beq_iff_eq] at h
  simpa using sameBytes_go w a b ha hb h.1 _ 0 h.2

/-! ## Chunk literals -/

theorem chain_spec (c : Nat) : ∀ n cs, (chain c n cs).wf = true ∧
    (chain c n cs).toList = chunksBytes c n cs
  | _, [] => ⟨rfl, rfl⟩
  | n, [x] => ⟨rfl, by simp [chain, toList, chunksBytes]⟩
  | n, x :: y :: ys => by
    obtain ⟨h1, h2⟩ := chain_spec c (n - c) (y :: ys)
    refine ⟨wf_node.2 ⟨rfl, rfl, h1⟩, ?_⟩
    simp only [chain, toList, h2, chunksBytes]

theorem chunksBytes_append (c : Nat) : ∀ (xs ys : List Nat) n,
    chunksBytes c n (xs ++ ys) = chunksBytes c n xs ++ chunksBytes c (n - c * xs.length) ys
  | [], ys, n => by simp [chunksBytes]
  | x :: xs, ys, n => by
    simp only [List.cons_append, chunksBytes, chunksBytes_append c xs ys (n - c),
      List.append_assoc, List.length_cons, Nat.mul_succ, Nat.sub_sub, Nat.add_comm c]

theorem chunksBytes_min (c : Nat) : ∀ (xs : List Nat) n,
    chunksBytes c (min n (c * xs.length)) xs = chunksBytes c n xs
  | [], n => rfl
  | x :: xs, n => by
    simp only [chunksBytes, List.length_cons, Nat.mul_succ]
    rw [← chunksBytes_min c xs (n - c)]
    congr 2
    · omega
    · omega

theorem ofChunksAux_spec (c : Nat) : ∀ fuel n (cs : List Nat), (ofChunksAux c fuel n cs
    cs.length).wf = true ∧ (ofChunksAux c fuel n cs cs.length).toList = chunksBytes c n cs
  | 0, n, cs => chain_spec c n cs
  | fuel + 1, n, cs => by
    simp only [ofChunksAux]
    split
    · exact chain_spec c n cs
    · rename_i hk
      have hp := leftLeaves_lt (k := cs.length) (by omega)
      generalize leftLeaves cs.length = p at hp ⊢
      have hlt : (cs.take p).length = p := by simp; omega
      have hdt : (cs.drop p).length = cs.length - p := by simp
      obtain ⟨h1, h2⟩ := ofChunksAux_spec c fuel (min n (p * c)) (cs.take p)
      obtain ⟨h3, h4⟩ := ofChunksAux_spec c fuel (n - p * c) (cs.drop p)
      rw [hlt] at h1 h2
      rw [hdt] at h3 h4
      refine ⟨wf_node.2 ⟨rfl, h1, h3⟩, ?_⟩
      simp only [toList, h2, h4]
      conv => rhs; rw [← List.take_append_drop p cs]
      rw [chunksBytes_append, hlt, ← chunksBytes_min c (cs.take p) n, hlt, Nat.mul_comm p c]

theorem ofChunks_spec (c n : Nat) (cs : List Nat) :
    (ofChunks c n cs).wf = true ∧ (ofChunks c n cs).toList = chunksBytes c n cs :=
  ofChunksAux_spec c 64 n cs

/-! ## Compiled comparison -/

theorem toList_eq_of_eqByteArray (t : KBytes) (b : ByteArray) (h : t.eqByteArray b = true) :
    t.toByteArray = b := by
  simp only [eqByteArray, beq_iff_eq] at h
  cases b with | mk data => cases data with | mk l => simp only [toByteArray, h]

end Silmaril.Proofs.Prelude.Bytes
