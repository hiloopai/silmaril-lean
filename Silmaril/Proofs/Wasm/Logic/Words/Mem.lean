module

public import Silmaril.Wasm.Logic.Words.Defs
public import Silmaril.Wasm.Logic.Memory.Thms

/-!
# `i32` words and arrays in linear memory: lemmas

Reading and writing words (`load_wd`, `store_wr`, `wd_wr_same`, `wd_wr_ne`, copied from the
LRAT example's `Silmaril.Proofs.Wasm.Examples.LRAT.Rules` and generalised to any memory size), the
array view (`words_wr`: a write inside the segment is `List.set`; `getElem_words`), and the
frame of a write (`sameOutside_wr`: bytes outside the segment are unchanged).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Words

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Logic.Core (storeLE load_eq store_eq size_store toList_writeBytes getElem?_splice)

variable {B : ByteArray}

/-! ## Words -/

theorem load_wd {a : Nat} (h : a + 4 ≤ B.size) : Memory.load B a 4 = some (wd B a) := by
  rw [wd, load_eq h]
  rfl

theorem store_wr {a : Nat} (v : BitVec 32) (h : a + 4 ≤ B.size) :
    Memory.store B a (count := 4) v = some (wr B a v) := by
  rw [store_eq v h]
  rfl

theorem size_wr {a : Nat} (v : BitVec 32) (h : a + 4 ≤ B.size) : (wr B a v).size = B.size :=
  size_store (store_wr v h)

/-- Read after write at the same address. -/
theorem wd_wr_same {a : Nat} (v : BitVec 32) (h : a + 4 ≤ B.size) : wd (wr B a v) a = v := by
  have hl := Silmaril.Wasm.Logic.Core.load_store_same (n := 4) (store_wr (B := B) v h)
  simp only [wd, hl, Option.getD_some]

/-- Read after write at a disjoint address. -/
theorem wd_wr_ne {a b : Nat} (v : BitVec 32) (h : a + 4 ≤ B.size) (hd : a + 4 ≤ b ∨ b + 4 ≤ a) :
    wd (wr B a v) b = wd B b := by
  have hl := Silmaril.Wasm.Logic.Core.load_store_disjoint (n := 4) (b := b) (m := 4)
    (store_wr (B := B) v h) hd
  simp only [wd, hl]

/-! ## Arrays -/

@[simp] theorem length_words (p n : Nat) : (words B p n).length = n := by simp [words]

theorem getElem_words {p n k : Nat} (hk : k < n) :
    (words B p n)[k]'(by simp [hk]) = wd B (p + 4 * k) := by
  simp [words]

theorem getElem?_words {p n k : Nat} (hk : k < n) : (words B p n)[k]? = some (wd B (p + 4 * k)) := by
  simp [words, hk]

theorem getD_words {p n k : Nat} (hk : k < n) : (words B p n).getD k 0 = wd B (p + 4 * k) := by
  simp [List.getD_eq_getElem?_getD, getElem?_words hk]

/-- **A write inside the segment** is `List.set` on the array. -/
theorem words_wr {p n k : Nat} (v : BitVec 32) (hk : k < n) (hb : p + 4 * n ≤ B.size) :
    words (wr B (p + 4 * k) v) p n = (words B p n).set k v := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [length_words] at h₁
  rw [getElem_words h₁, List.getElem_set]
  split
  · subst_vars
    exact wd_wr_same v (by omega)
  · rw [getElem_words h₁]
    exact wd_wr_ne v (by omega) (by omega)

/-- A write outside the segment leaves the array unchanged. -/
theorem words_wr_out {p n a : Nat} (v : BitVec 32) (ha : a + 4 ≤ B.size)
    (hd : a + 4 ≤ p ∨ p + 4 * n ≤ a) : words (wr B a v) p n = words B p n := by
  unfold words
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < n := List.mem_range.1 hk
  exact wd_wr_ne v ha (by omega)

/-- An array segment splits into two consecutive ones. -/
theorem words_append (p m r : Nat) : words B p (m + r) = words B p m ++ words B (p + 4 * m) r := by
  apply List.ext_getElem (by simp)
  intro k h₁ h₂
  simp only [length_words] at h₁
  rw [getElem_words h₁, List.getElem_append]
  split
  · rename_i hk
    simp only [length_words] at hk
    rw [getElem_words hk]
  · rename_i hk
    simp only [length_words] at hk
    have hk' : k - m < r := by omega
    simp only [length_words, getElem_words hk']
    congr 1
    omega

/-! ## The frame of a write -/

theorem SameOutside.refl (B : ByteArray) (p len : Nat) : SameOutside B B p len :=
  ⟨rfl, fun _ _ => rfl⟩

theorem SameOutside.trans {B₁ B₂ B₃ : ByteArray} {p len : Nat} (h₁ : SameOutside B₁ B₂ p len)
    (h₂ : SameOutside B₂ B₃ p len) : SameOutside B₁ B₃ p len :=
  ⟨h₂.1.trans h₁.1, fun i hi => (h₂.2 i hi).trans (h₁.2 i hi)⟩

/-- Widening the region of a `SameOutside`. -/
theorem SameOutside.mono {B₁ B₂ : ByteArray} {p len q m : Nat} (h : SameOutside B₁ B₂ p len)
    (hq : q ≤ p) (hm : p + len ≤ q + m) : SameOutside B₁ B₂ q m :=
  ⟨h.1, fun i hi => h.2 i (by omega)⟩

/-- A write of a word inside `[p, p + len)` changes nothing outside it. -/
theorem sameOutside_wr {p len a : Nat} (v : BitVec 32) (ha : a + 4 ≤ B.size) (hp : p ≤ a)
    (hl : a + 4 ≤ p + len) : SameOutside B (wr B a v) p len := by
  have hw : Memory.writeBytes B a (Memory.encodeLE 4 v.toNat) = some (wr B a v) := store_wr v ha
  obtain ⟨hb, hL⟩ := toList_writeBytes hw
  have hsz : (Memory.encodeLE 4 v.toNat).size = 4 := Memory.encodeLE_size 4 v.toNat
  have hlen : a + (Memory.encodeLE 4 v.toNat).data.toList.length ≤ B.data.toList.length := by
    simp only [Array.length_toList, ByteArray.size_data]
    exact (show (Memory.encodeLE 4 v.toNat).data.size = 4 from hsz) ▸ ha
  refine ⟨size_wr v ha, fun i hi => ?_⟩
  rw [hL, show (Memory.encodeLE 4 v.toNat).size = (Memory.encodeLE 4 v.toNat).data.toList.length
    from rfl, getElem?_splice hlen]
  have hd : (Memory.encodeLE 4 v.toNat).data.toList.length = 4 := by
    simp only [Array.length_toList, ByteArray.size_data]; exact hsz
  split
  · omega
  · rfl

/-- Equal sizes and equal bytes outside the segment give equal words outside it. -/
theorem SameOutside.wd_eq {B' : ByteArray} {p len a : Nat} (h : SameOutside B B' p len)
    (ha : a + 4 ≤ p ∨ p + len ≤ a) : wd B' a = wd B a := by
  by_cases hb : a + 4 ≤ B.size
  · have hb' : a + 4 ≤ B'.size := h.1 ▸ hb
    have hr : Silmaril.Wasm.Logic.Core.bytesAt B' ⟨a, 4⟩ = Silmaril.Wasm.Logic.Core.bytesAt B ⟨a, 4⟩ := by
      apply List.ext_getElem?
      intro i
      rw [Silmaril.Wasm.Logic.Core.getElem?_bytesAt, Silmaril.Wasm.Logic.Core.getElem?_bytesAt]
      dsimp only
      split
      · exact h.2 _ (by omega)
      · rfl
    rw [wd, wd, load_eq hb, load_eq hb', hr]
  · have hl : Memory.load B a 4 = none := Silmaril.Wasm.Logic.Core.load_eq_none (by omega)
    have hl' : Memory.load B' a 4 = none := Silmaril.Wasm.Logic.Core.load_eq_none (by rw [h.1]; omega)
    rw [wd, wd, hl, hl']

/-- Arrays outside the segment of a `SameOutside` are unchanged. -/
theorem SameOutside.words_eq {B' : ByteArray} {p len q m : Nat} (h : SameOutside B B' p len)
    (hd : q + 4 * m ≤ p ∨ p + len ≤ q) : words B' q m = words B q m := by
  unfold words
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < m := List.mem_range.1 hk
  exact h.wd_eq (by omega)

/-! ## Frames of two regions -/

theorem SameOutside.two {B' : ByteArray} {p len : Nat} (h : SameOutside B B' p len)
    (q len' : Nat) : SameOutside2 B B' p len q len' :=
  ⟨h.1, fun i hi _ => h.2 i hi⟩

theorem SameOutside.two' {B' : ByteArray} {q len' : Nat} (h : SameOutside B B' q len')
    (p len : Nat) : SameOutside2 B B' p len q len' :=
  ⟨h.1, fun i _ hi => h.2 i hi⟩

theorem SameOutside2.refl (B : ByteArray) (p len q len' : Nat) : SameOutside2 B B p len q len' :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem SameOutside2.trans {B₁ B₂ B₃ : ByteArray} {p len q len' : Nat}
    (h₁ : SameOutside2 B₁ B₂ p len q len') (h₂ : SameOutside2 B₂ B₃ p len q len') :
    SameOutside2 B₁ B₃ p len q len' :=
  ⟨h₂.1.trans h₁.1, fun i hi hj => (h₂.2 i hi hj).trans (h₁.2 i hi hj)⟩

/-- Widening both regions. -/
theorem SameOutside2.mono {B₁ B₂ : ByteArray} {p len q len' p₁ l₁ q₁ l₁' : Nat}
    (h : SameOutside2 B₁ B₂ p len q len') (hp : p₁ ≤ p) (hl : p + len ≤ p₁ + l₁)
    (hq : q₁ ≤ q) (hl' : q + len' ≤ q₁ + l₁') : SameOutside2 B₁ B₂ p₁ l₁ q₁ l₁' :=
  ⟨h.1, fun i hi hj => h.2 i (by omega) (by omega)⟩

/-- Equal sizes and equal bytes outside two regions give equal words outside both. -/
theorem SameOutside2.wd_eq {B' : ByteArray} {p len q len' a : Nat}
    (h : SameOutside2 B B' p len q len') (ha : a + 4 ≤ p ∨ p + len ≤ a)
    (hb : a + 4 ≤ q ∨ q + len' ≤ a) : wd B' a = wd B a := by
  by_cases hB : a + 4 ≤ B.size
  · have hB' : a + 4 ≤ B'.size := h.1 ▸ hB
    have hr : Silmaril.Wasm.Logic.Core.bytesAt B' ⟨a, 4⟩ = Silmaril.Wasm.Logic.Core.bytesAt B ⟨a, 4⟩ := by
      apply List.ext_getElem?
      intro i
      rw [Silmaril.Wasm.Logic.Core.getElem?_bytesAt, Silmaril.Wasm.Logic.Core.getElem?_bytesAt]
      dsimp only
      split
      · exact h.2 _ (by omega) (by omega)
      · rfl
    rw [wd, wd, load_eq hB, load_eq hB', hr]
  · have hl : Memory.load B a 4 = none := Silmaril.Wasm.Logic.Core.load_eq_none (by omega)
    have hl' : Memory.load B' a 4 = none := Silmaril.Wasm.Logic.Core.load_eq_none (by rw [h.1]; omega)
    rw [wd, wd, hl, hl']

/-- Arrays outside both regions are unchanged. -/
theorem SameOutside2.words_eq {B' : ByteArray} {p len q len' r m : Nat}
    (h : SameOutside2 B B' p len q len') (hd : r + 4 * m ≤ p ∨ p + len ≤ r)
    (hd' : r + 4 * m ≤ q ∨ q + len' ≤ r) : words B' r m = words B r m := by
  unfold words
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < m := List.mem_range.1 hk
  exact h.wd_eq (by omega) (by omega)

end Silmaril.Wasm.Logic.Words
