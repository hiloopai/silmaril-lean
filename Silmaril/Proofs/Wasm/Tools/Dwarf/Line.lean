module

public import Silmaril.Wasm.Tools.Dwarf.Line.Defs

/-!
# Raw proofs: the line program's special opcodes and the binary search of the lookup

Restated in `Silmaril.Wasm.Tools.Dwarf.Line.Thms`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Tools.Dwarf

open Silmaril.Wasm.Tools.Dwarf

/-! ## Special opcodes -/

theorem lineAdvance_line (r : Regs) (d : Int) (h : r.line + d < 2 ^ 64) :
    (lineAdvance r d).line = (r.line + d).toNat := by
  unfold lineAdvance
  split
  · simp only; omega
  · simp only
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem lineAdvance_other (r : Regs) (d : Int) :
    (lineAdvance r d).address = r.address ∧ (lineAdvance r d).opIndex = r.opIndex ∧
      (lineAdvance r d).file = r.file ∧ (lineAdvance r d).column = r.column ∧
      (lineAdvance r d).tombstone = r.tombstone ∧ (lineAdvance r d).endSeq = r.endSeq := by
  unfold lineAdvance
  split <;> simp

/-- A special opcode with one operation per instruction (DWARF §6.2.5.1). -/
theorem specialRegs_spec (h : LineHeader) (r : Regs) (op : Nat) (hm : h.maxOps = 1)
    (ht : r.tombstone = false)
    (hadv : h.minInstLen * ((op - h.opcodeBase) / h.lineRange) < 2 ^ 64)
    (hov : r.address + h.minInstLen * ((op - h.opcodeBase) / h.lineRange) < 2 ^ 64)
    (hl : r.line + (h.lineBase + ((op - h.opcodeBase) % h.lineRange : Nat)) < 2 ^ 64) :
    ∃ r', specialRegs h r op = .ok r' ∧
      r'.address = (r.address + h.minInstLen * ((op - h.opcodeBase) / h.lineRange)) % 2 ^ (8 * h.addressSize) ∧
      r'.opIndex = 0 ∧
      r'.line = (r.line + (h.lineBase + ((op - h.opcodeBase) % h.lineRange : Nat))).toNat ∧
      r'.file = r.file ∧ r'.column = r.column ∧ r'.tombstone = r.tombstone ∧ r'.endSeq = r.endSeq := by
  unfold specialRegs opAdvance addSizedChecked
  simp only [ht, hm, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
  rw [Nat.mod_eq_of_lt hadv]
  have hnot : ¬ 2 ^ 64 ≤ r.address + h.minInstLen * ((op - h.opcodeBase) / h.lineRange) := by omega
  simp only [hnot, ↓reduceIte, Except.map, bind, Except.bind, pure, Except.pure]
  refine ⟨_, rfl, ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := lineAdvance_other
    { address := (r.address + h.minInstLen * ((op - h.opcodeBase) / h.lineRange)) % 2 ^ (8 * h.addressSize),
      file := r.file, line := r.line, column := r.column, endSeq := r.endSeq : Regs }
    (h.lineBase + ((op - h.opcodeBase) % h.lineRange : Nat))
  refine ⟨a1, a2, ?_, a3, a4, a5, a6⟩
  exact lineAdvance_line _ _ hl

/-! ## Binary search -/

/-- The invariant of the search window `[base, base + size)`: inside the array, nonempty, the
element at `base` is not greater (unless `base = 0`), and the element just past the window is
greater (unless the window reaches the end). -/
def Inv {α : Type} [Inhabited α] (xs : Array α) (cmp : α → Ordering) (base size : Nat) : Prop :=
  base + size ≤ xs.size ∧ 1 ≤ size ∧ (base = 0 ∨ cmp xs[base]! ≠ .gt) ∧
    (base + size = xs.size ∨ cmp xs[base + size]! = .gt)

/-- The comparison is monotone along the array. -/
def Sorted {α : Type} [Inhabited α] (xs : Array α) (cmp : α → Ordering) : Prop :=
  ∀ i j, i ≤ j → j < xs.size → ordRank (cmp xs[i]!) ≤ ordRank (cmp xs[j]!)

theorem gt_of_le {α : Type} [Inhabited α] (xs : Array α) (cmp : α → Ordering) (hs : Sorted xs cmp)
    (i j : Nat) (hij : i ≤ j) (hj : j < xs.size) (hi : cmp xs[i]! = .gt) : cmp xs[j]! = .gt := by
  have := hs i j hij hj
  rw [hi] at this
  revert this
  cases cmp xs[j]! <;> simp [ordRank]

theorem lt_of_le {α : Type} [Inhabited α] (xs : Array α) (cmp : α → Ordering) (hs : Sorted xs cmp)
    (i j : Nat) (hij : i ≤ j) (hj : j < xs.size) (hi : cmp xs[j]! = .lt) : cmp xs[i]! = .lt := by
  have := hs i j hij hj
  rw [hi] at this
  revert this
  cases cmp xs[i]! <;> simp [ordRank]

/-- The loop keeps the invariant and halves the window. -/
theorem bsLoop_inv {α : Type} [Inhabited α] (xs : Array α) (cmp : α → Ordering) (hs : Sorted xs cmp) :
    ∀ (k base size : Nat), Inv xs cmp base size → size ≤ 2 ^ k →
      Inv xs cmp (bsLoop xs cmp k base size).1 (bsLoop xs cmp k base size).2 ∧
        (bsLoop xs cmp k base size).2 ≤ 1
  | 0, base, size, hi, hk => by
    simp only [bsLoop]
    refine ⟨hi, ?_⟩
    simpa using hk
  | k + 1, base, size, hi, hk => by
    simp only [bsLoop]
    split
    · rename_i h1; exact ⟨hi, h1⟩
    · rename_i h1
      obtain ⟨i1, i2, i3, i4⟩ := hi
      have hmid : base + size / 2 < xs.size := by omega
      apply bsLoop_inv xs cmp hs k
      · split
        · rename_i hg
          have hg' : cmp xs[base + size / 2]! = .gt := by simpa using hg
          refine ⟨by omega, by omega, i3, Or.inr ?_⟩
          exact gt_of_le xs cmp hs _ _ (by omega) (by omega) hg'
        · rename_i hg
          have hg' : cmp xs[base + size / 2]! ≠ .gt := by simpa using hg
          refine ⟨by omega, by omega, Or.inr hg', ?_⟩
          rw [show base + size / 2 + (size - size / 2) = base + size by omega]
          exact i4
      · rw [Nat.pow_succ] at hk; omega

/-- The last step of the search, at the one candidate `base` left. -/
theorem bsFinal_spec {α : Type} [Inhabited α] (xs : Array α) (cmp : α → Ordering)
    (hs : Sorted xs cmp) (base : Nat) (hinv : Inv xs cmp base 1) :
    match (if cmp xs[base]! == .eq then .ok base
        else .error (base + (if cmp xs[base]! == .lt then 1 else 0)) : Except Nat Nat) with
    | .ok i => i < xs.size ∧ cmp xs[i]! = .eq
    | .error j => j ≤ xs.size ∧ (∀ i, i < j → cmp xs[i]! = .lt) ∧
        (∀ i, j ≤ i → i < xs.size → cmp xs[i]! = .gt) := by
  obtain ⟨i1, -, i3, i4⟩ := hinv
  have hb : base < xs.size := by omega
  cases hc : cmp xs[base]! with
  | eq =>
    simp only [show (Ordering.eq == Ordering.eq) = true from rfl, ↓reduceIte]
    exact ⟨hb, hc⟩
  | lt =>
    simp only [show (Ordering.lt == Ordering.eq) = false from rfl,
      show (Ordering.lt == Ordering.lt) = true from rfl, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by omega, fun i hi => lt_of_le xs cmp hs i base (by omega) hb hc, fun i hi hi' => ?_⟩
    rcases i4 with h | h
    · omega
    · exact gt_of_le xs cmp hs _ _ hi hi' h
  | gt =>
    simp only [show (Ordering.gt == Ordering.eq) = false from rfl,
      show (Ordering.gt == Ordering.lt) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      Nat.add_zero]
    have hb0 : base = 0 := i3.resolve_right (fun h => h hc)
    refine ⟨by omega, fun i hi => absurd hi (by omega), fun i _ hi' => ?_⟩
    exact gt_of_le xs cmp hs base i (by omega) hi' hc

/-- **Rust's `binary_search_by`** on an array sorted for the comparison (and shorter than
`2^64`): `ok i` at an equal element, or `error j` where every element before `j` is less and
every element from `j` is greater. -/
theorem binarySearch_spec {α : Type} [Inhabited α] (xs : Array α) (cmp : α → Ordering)
    (hs : Sorted xs cmp) (hn : xs.size ≤ 2 ^ 64) :
    match binarySearch xs cmp with
    | .ok i => i < xs.size ∧ cmp xs[i]! = .eq
    | .error j => j ≤ xs.size ∧ (∀ i, i < j → cmp xs[i]! = .lt) ∧
        (∀ i, j ≤ i → i < xs.size → cmp xs[i]! = .gt) := by
  unfold binarySearch
  by_cases h0 : xs.size = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    exact ⟨by omega, fun i hi => absurd hi (by omega), fun i _ hi => absurd hi (by omega)⟩
  · have h0' : (xs.size == 0) = false := by simpa using h0
    have hinv : Inv xs cmp 0 xs.size := ⟨by omega, by omega, Or.inl rfl, Or.inl (by omega)⟩
    have hfin : Inv xs cmp (bsLoop xs cmp 64 0 xs.size).1 (bsLoop xs cmp 64 0 xs.size).2 ∧
        (bsLoop xs cmp 64 0 xs.size).2 ≤ 1 := bsLoop_inv xs cmp hs 64 0 xs.size hinv hn
    have hone : (bsLoop xs cmp 64 0 xs.size).2 = 1 := by
      have h1 : 1 ≤ (bsLoop xs cmp 64 0 xs.size).2 := hfin.1.2.1
      omega
    have hlast : Inv xs cmp (bsLoop xs cmp 64 0 xs.size).1 1 := hone ▸ hfin.1
    simp only [h0', Bool.false_eq_true, ↓reduceIte]
    exact bsFinal_spec xs cmp hs _ hlast

end Silmaril.Proofs.Wasm.Tools.Dwarf

end
