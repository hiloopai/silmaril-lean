module

public import Silmaril.Data.Layout.Bits.Defs

/-!
# Bit ranges: read after write, framing, validity

`BitRange.testBit_get`, `BitRange.testBit_set` describe the operations bitwise; from them
`get_set_self`, `get_set_disjoint`, `set_get`, `set_lt`. For specifications:
`WordSpec.get?_set?_self`, `WordSpec.get?_set?_other`, `WordSpec.valid_set?` and
`WordSpec.keeps_set?`.
-/

@[expose] public section

namespace Silmaril.Data.Layout

namespace BitRange

theorem testBit_get (r : BitRange) (v i : Nat) :
    (r.get v).testBit i = (decide (i < r.width) && v.testBit (r.lo + i)) := by
  simp [get]

theorem testBit_set (r : BitRange) (v x j : Nat) :
    (r.set v x).testBit j =
      if r.lo ≤ j ∧ j < r.lo + r.width then x.testBit (j - r.lo) else v.testBit j := by
  simp only [set, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  by_cases h : r.lo ≤ j ∧ j < r.lo + r.width
  · have h1 : j ≥ r.lo := h.1
    have h2 : j - r.lo < r.width := by omega
    simp only [h, and_self, ite_true, h2, decide_true, Bool.true_and,
      show r.lo + (j - r.lo) = j by omega]
    cases v.testBit j <;> cases x.testBit (j - r.lo) <;> rfl
  · simp only [h, ite_false]
    have : (decide (j ≥ r.lo) && (decide (j - r.lo < r.width) &&
        (v.testBit (r.lo + (j - r.lo)) ^^ x.testBit (j - r.lo)))) = false := by
      by_cases h1 : j ≥ r.lo
      · have : ¬ (j - r.lo < r.width) := by omega
        simp [this]
      · simp [h1]
    rw [this]; simp

theorem get_set_self (r : BitRange) (v x : Nat) : r.get (r.set v x) = x % 2 ^ r.width := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_get, testBit_set, Nat.testBit_mod_two_pow]
  by_cases hi : i < r.width
  · simp [hi, show r.lo ≤ r.lo + i ∧ r.lo + i < r.lo + r.width by omega]
  · simp [hi]

theorem get_set_disjoint {r s : BitRange} (h : r.Disjoint s) (v x : Nat) :
    s.get (r.set v x) = s.get v := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_get, testBit_get, testBit_set]
  by_cases hi : i < s.width
  · have : ¬ (r.lo ≤ s.lo + i ∧ s.lo + i < r.lo + r.width) := by
      unfold Disjoint at h; omega
    simp [this]
  · simp [hi]

theorem set_get (r : BitRange) (v : Nat) : r.set v (r.get v) = v := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_set]
  split
  · rw [testBit_get]; simp [show j - r.lo < r.width by omega, show r.lo + (j - r.lo) = j by omega]
  · rfl

theorem set_lt {r : BitRange} {N v : Nat} (hv : v < 2 ^ N) (hr : r.lo + r.width ≤ N) (x : Nat) :
    r.set v x < 2 ^ N := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_set]
  split
  · omega
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hi))

theorem Disjoint.symm {r s : BitRange} (h : r.Disjoint s) : s.Disjoint r := by
  unfold Disjoint at *; omega

end BitRange

namespace WordSpec

theorem mem_of_item? {S : WordSpec} {name : String} {it : BitItem} (h : S.item? name = some it) :
    it ∈ S.items ∧ it.name = name := by
  simp only [item?] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem pairwise_disjoint_of_ne {l : List BitItem}
    (hp : l.Pairwise fun a b => a.range.Disjoint b.range) {a b : BitItem} (ha : a ∈ l)
    (hb : b ∈ l) (hne : a ≠ b) : a.range.Disjoint b.range := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.pairwise_cons] at hp
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hne
    · exact hp.1 b hb
    · exact (hp.1 a ha).symm
    · exact ih hp.2 ha hb

theorem disjoint_of_ne {S : WordSpec} (hS : S.WF) {a b : BitItem} (ha : a ∈ S.items)
    (hb : b ∈ S.items) (hne : a ≠ b) : a.range.Disjoint b.range :=
  pairwise_disjoint_of_ne hS.2 ha hb hne

theorem get?_set?_self {S : WordSpec} {name : String} {v x v' : Nat}
    (h : S.set? name v x = some v') {it : BitItem} (hit : S.item? name = some it) :
    S.get? name v' = some (x % 2 ^ it.range.width) := by
  simp only [set?, hit, Option.bind_some] at h
  split at h
  · cases h; simp [get?, hit, BitRange.get_set_self]
  · cases h

/-- Setting one item of a well-formed spec leaves every other item unchanged. -/
theorem get?_set?_other {S : WordSpec} (hS : S.WF) {name name' : String} (hne : name ≠ name')
    {v x v' : Nat} (h : S.set? name v x = some v') : S.get? name' v' = S.get? name' v := by
  simp only [set?, Option.bind_eq_some_iff] at h
  obtain ⟨it, hit, h⟩ := h
  split at h
  · cases h
    simp only [get?]
    cases hb : S.item? name' with
    | none => rfl
    | some b =>
      have h1 := mem_of_item? hit
      have h2 := mem_of_item? hb
      simp only [Option.map_some, Option.some.injEq]
      exact BitRange.get_set_disjoint
        (disjoint_of_ne hS h1.1 h2.1 (fun e => hne (h1.2.symm.trans (e ▸ h2.2)))) _ _
  · cases h

/-- Setting a flag or value item keeps a valid word valid and keeps the reserved bits. -/
theorem valid_set? {S : WordSpec} (hS : S.WF) {name : String} {v x v' : Nat}
    (hv : S.Valid v) (h : S.set? name v x = some v') : S.Valid v' ∧ S.Keeps v v' := by
  simp only [set?, Option.bind_eq_some_iff] at h
  obtain ⟨it, hit, h⟩ := h
  have hmem := (mem_of_item? hit).1
  split at h
  · rename_i hrole
    cases h
    have other : ∀ b ∈ S.items, b.role = .zero ∨ b.role = .reserved →
        b.range.get (it.range.set v x) = b.range.get v := by
      intro b hb hr
      have hne : it ≠ b := by
        rintro rfl; rcases hrole with h1 | h1 <;> rcases hr with h2 | h2 <;>
          rw [h1] at h2 <;> cases h2
      exact BitRange.get_set_disjoint (disjoint_of_ne hS hmem hb hne) _ _
    refine ⟨⟨BitRange.set_lt hv.1 (hS.1 it hmem) x, fun b hb hz => ?_⟩, fun b hb hr => ?_⟩
    · rw [other b hb (.inl hz)]; exact hv.2 b hb hz
    · exact other b hb (.inr hr)
  · cases h

end WordSpec

end Silmaril.Data.Layout
