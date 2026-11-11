module

public import Silmaril.Wasm.Auto2.VCSort.Defs
public import Silmaril.Wasm.Auto2.VCGen.Thms

/-!
# Insertion sort through VC generator 4: the conditions

The 15 conditions of `insertion_sort` against `sortSpecV` (outer loop entry and exit, the key's
load, inner loop entry, the two inner exits with their stores, outer invariant and variant, the
shift's load and store, inner invariant and variant), each a lemma over the words of the
memories, closed with the list lemmas of the hand proof (`hole_shift`, `hole_place_perm`,
`hole_place_sorted`, `Silmaril.WasmSpec.InsertionSort`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCSort

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.InsertionSort (Sorts hole hole_self hole_shift getElem_hole_pred
  hole_place_perm hole_place_sorted length_hole)

/-! ## Memory accesses -/

theorem ldW_wd (B : ByteArray) (a : Nat) : ldW 32 4 .unsigned B a = wd B a := by
  simp [ldW, rd, wd]

theorem stW_wr {B : ByteArray} {a : Nat} (v : BitVec 32) (h : a + 4 ≤ B.size) :
    stW 32 4 B a v = wr B a v := by
  simp [stW, store_wr v h]

/-- An address `p + 4 k` that does not wrap. -/
theorem addr_toNat {p k : BitVec 32} (h : p.toNat + 4 * k.toNat < 2 ^ 32) :
    (p + k * 4#32).toNat = p.toNat + 4 * k.toNat := by
  bv_omega

theorem toNat_succ {i n : BitVec 32} (h : i.toNat < n.toNat) : (i + 1#32).toNat = i.toNat + 1 := by
  have := n.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toNat_pred {j : BitVec 32} (h : j ≠ 0#32) : (j - 1#32).toNat = j.toNat - 1 := by
  have : j.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-! ## Facts of the invariants -/

theorem sortFns_pre {B : ByteArray} {p n : BitVec 32} : sortFns.pr 0 B [p, n] ↔ PreS B p n :=
  Iff.rfl

theorem sortFns_post {B B' : ByteArray} {p n : BitVec 32} :
    sortFns.pr2 0 B' B [p, n] ↔ Sorts B B' p.toNat n.toNat := Iff.rfl

theorem sortFns_out {B B' : ByteArray} {p n i : BitVec 32} :
    sortFns.pr2 1 B' B [p, n, i] ↔ OutS B B' p n i := Iff.rfl

theorem sortFns_in {B B' : ByteArray} {p n i j key : BitVec 32} :
    sortFns.pr2 2 B' B [p, n, i, j, key] ↔ InS B B' p n i j key := Iff.rfl

/-- A word `k ≤ n` of the segment is in a memory of the same size. -/
theorem bound_k {B B' : ByteArray} {p n k : BitVec 32} (hp : PreS B p n) (hs : B'.size = B.size)
    (hk : k.toNat < n.toNat) : (p + k * 4#32).toNat + 4 ≤ B'.size := by
  obtain ⟨h₁, h₂⟩ := hp
  rw [addr_toNat (by omega), hs]
  omega

/-! ## The conditions -/

theorem c_entry {M0 : ByteArray} {p n : BitVec 32} (_h : sortFns.pr 0 M0 [p, n]) :
    sortFns.pr2 1 M0 M0 [p, n, 1#32] := by
  refine sortFns_out.mpr ⟨by simp, by simp, SameOutside.refl _ _ _, List.Perm.refl _,
    sortedS_take_one _⟩

theorem c_exit {M8 M0 : ByteArray} {p n i : BitVec 32}
    (h : n.toNat ≤ i.toNat ∧ sortFns.pr2 1 M8 M0 [p, n, i] ∧ sortFns.pr 0 M0 [p, n]) :
    sortFns.pr2 0 M8 M0 [p, n] := by
  obtain ⟨hni, ⟨-, -, hso, hperm, hsort⟩, -⟩ := h
  exact sortFns_post.mpr ⟨hso, sortedS_of_take hsort (by simpa using hni), hperm⟩

theorem c_key_bound {M8 M0 : ByteArray} {p n i : BitVec 32}
    (h : ¬n.toNat ≤ i.toNat ∧ sortFns.pr2 1 M8 M0 [p, n, i] ∧ sortFns.pr 0 M0 [p, n]) :
    (p + i * 4#32).toNat + 4 ≤ M8.size := by
  obtain ⟨hni, ⟨-, -, hso, -, -⟩, hp⟩ := h
  exact bound_k hp hso.1 (by omega)

theorem c_inner_entry {M8 M0 : ByteArray} {p n i key : BitVec 32}
    (h : key = ldW 32 4 .unsigned M8 ((p + i * 4#32).toNat + 0) ∧ ¬n.toNat ≤ i.toNat ∧
      sortFns.pr2 1 M8 M0 [p, n, i] ∧ sortFns.pr 0 M0 [p, n]) :
    sortFns.pr2 2 M8 M0 [p, n, i, i, key] := by
  obtain ⟨hkey, hni, ⟨h1, -, hso, hperm, hsort⟩, hp⟩ := h
  have hi : i.toNat < n.toNat := by omega
  have ha : (p + i * 4#32).toNat = p.toNat + 4 * i.toNat := addr_toNat (by have := hp.2; omega)
  refine sortFns_in.mpr ⟨words M8 p.toNat n.toNat, by simp, hperm, hsort, h1, hi, ?_, le_rfl, hso,
    (hole_self _ _).symm, by simp⟩
  rw [hkey, Nat.add_zero, ldW_wd, ha, getD_words hi]

theorem in_lt {M15 M0 : ByteArray} {p n i j key : BitVec 32} (hin : InS M0 M15 p n i j key) :
    j.toNat < n.toNat := by
  obtain ⟨-, -, -, -, -, hi, -, hj, -, -, -⟩ := hin
  omega

/-- The words at `p + 4 j` and `p + 4 (j - 1)` are in the current memory of the inner loop. -/
theorem in_bound {M15 M0 : ByteArray} {p n i j key : BitVec 32} (hin : InS M0 M15 p n i j key)
    (hp : PreS M0 p n) : (p + j * 4#32).toNat + 4 ≤ M15.size := by
  obtain ⟨-, -, -, -, -, hi, -, hj, hso, -, -⟩ := hin
  exact bound_k hp hso.1 (by omega)

theorem in_bound_pred {M15 M0 : ByteArray} {p n i j key : BitVec 32} (hin : InS M0 M15 p n i j key)
    (hp : PreS M0 p n) (hj0 : j ≠ 0#32) : (p + (j - 1#32) * 4#32).toNat + 4 ≤ M15.size := by
  obtain ⟨-, -, -, -, -, hi, -, hj, hso, -, -⟩ := hin
  exact bound_k hp hso.1 (by rw [toNat_pred hj0]; omega)

/-- **Placing the key** at the hole re-establishes the outer invariant for `i + 1`. -/
theorem place {M15 M0 : ByteArray} {p n i j key : BitVec 32} (hin : InS M0 M15 p n i j key)
    (hp : PreS M0 p n) (hle : j = 0#32 ∨ (wd M15 (p.toNat + 4 * (j.toNat - 1))).toInt ≤ key.toInt) :
    OutS M0 (wr M15 (p.toNat + 4 * j.toNat) key) p n (i + 1#32) := by
  obtain ⟨ys, hlen, hperm, hsort, h1, hi, hkey, hj, hso, hw, hgt⟩ := hin
  have hp' := hp
  obtain ⟨hb, hw32⟩ := hp'
  have hi' : i.toNat < ys.length := by omega
  have hys : ys[i.toNat] = key := by
    rw [← hkey, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    rfl
  have hjb : p.toNat + 4 * j.toNat + 4 ≤ M15.size := by rw [hso.1]; omega
  have hwr : words (wr M15 (p.toNat + 4 * j.toNat) key) p.toNat n.toNat =
      (hole ys i.toNat j.toNat).set j.toNat ys[i.toNat] := by
    rw [words_wr key (by omega) (by rw [hso.1]; omega), hw, hys]
  have hle' : j.toNat = 0 ∨ (ys[j.toNat - 1]'(by omega)).toInt ≤ ys[i.toNat].toInt := by
    by_cases hj0 : j.toNat = 0
    · exact .inl hj0
    · show j.toNat = 0 ∨ (ys[j.toNat - 1]'(by omega)).toInt ≤ ys[i.toNat].toInt
      right
      have h : (wd M15 (p.toNat + 4 * (j.toNat - 1))).toInt ≤ key.toInt := by
        rcases hle with h0 | h
        · exact absurd (by simp [h0]) hj0
        · exact h
      have hj1 : 1 ≤ j.toNat := by omega
      rw [← getElem_hole_pred hj1 hj hi', hys]
      have := getElem_words (B := M15) (p := p.toNat) (k := j.toNat - 1) (n := n.toNat) (by omega)
      simp only [hw] at this
      rw [this]
      exact h
  refine ⟨by rw [toNat_succ hi]; omega, by rw [toNat_succ hi]; omega,
    hso.trans (sameOutside_wr key hjb (by omega) (by omega)), ?_, ?_⟩
  · rw [hwr]
    exact (hole_place_perm hj hi').trans hperm
  · rw [hwr, toNat_succ hi]
    exact hole_place_sorted hj hi' hsort (by rw [hys]; exact hgt) hle'

theorem c_place0 {M16 M15 M8 M0 : ByteArray} {p n i j key i' : BitVec 32}
    (h : i' = i + 1#32 ∧ M16 = stW 32 4 M15 ((p + j * 4#32).toNat + 0) key ∧ j = 0#32 ∧
      sortFns.pr2 2 M15 M0 [p, n, i, j, key] ∧
      key = ldW 32 4 .unsigned M8 ((p + i * 4#32).toNat + 0) ∧ ¬n.toNat ≤ i.toNat ∧
      sortFns.pr2 1 M8 M0 [p, n, i] ∧ sortFns.pr 0 M0 [p, n]) :
    sortFns.pr2 1 M16 M0 [p, n, i'] := by
  obtain ⟨rfl, rfl, hj0, hin, -, -, -, hp⟩ := h
  have hb := in_bound hin hp
  have hjn : j.toNat < n.toNat := in_lt hin
  have ha : (p + j * 4#32).toNat = p.toNat + 4 * j.toNat := by
    have := hp.2; exact addr_toNat (by omega)
  rw [Nat.add_zero, stW_wr key hb, ha]
  exact place hin hp (.inl hj0)

theorem c_place {M16 M15 M8 M0 : ByteArray} {p n i j key i' : BitVec 32}
    (h : i' = i + 1#32 ∧ M16 = stW 32 4 M15 ((p + j * 4#32).toNat + 0) key ∧
      (ldW 32 4 .unsigned M15 ((p + (j - 1#32) * 4#32).toNat + 0)).toInt ≤ key.toInt ∧
      j ≠ 0#32 ∧ sortFns.pr2 2 M15 M0 [p, n, i, j, key] ∧
      key = ldW 32 4 .unsigned M8 ((p + i * 4#32).toNat + 0) ∧ ¬n.toNat ≤ i.toNat ∧
      sortFns.pr2 1 M8 M0 [p, n, i] ∧ sortFns.pr 0 M0 [p, n]) :
    sortFns.pr2 1 M16 M0 [p, n, i'] := by
  obtain ⟨rfl, rfl, hle, hj0, hin, -, -, -, hp⟩ := h
  have hb := in_bound hin hp
  have hjn : j.toNat < n.toNat := in_lt hin
  have ha : (p + j * 4#32).toNat = p.toNat + 4 * j.toNat := by
    have := hp.2; exact addr_toNat (by omega)
  have ha' : (p + (j - 1#32) * 4#32).toNat = p.toNat + 4 * (j.toNat - 1) := by
    have := hp.2; rw [addr_toNat (by rw [toNat_pred hj0]; omega), toNat_pred hj0]
  rw [Nat.add_zero, ldW_wd, ha'] at hle
  rw [Nat.add_zero, stW_wr key hb, ha]
  exact place hin hp (.inr hle)

theorem c_var_out {i n i' : BitVec 32} (h : i' = i + 1#32) (hni : ¬n.toNat ≤ i.toNat) :
    (n - i').toNat < (n - i).toNat := by
  subst h
  bv_omega

/-- **The shift**: copying the word below the hole into it moves the hole down. -/
theorem shift {M15 M0 : ByteArray} {p n i j key : BitVec 32} (hin : InS M0 M15 p n i j key)
    (hp : PreS M0 p n) (hj0 : j ≠ 0#32)
    (hgt : ¬(wd M15 (p.toNat + 4 * (j.toNat - 1))).toInt ≤ key.toInt) :
    InS M0 (wr M15 (p.toNat + 4 * j.toNat) (wd M15 (p.toNat + 4 * (j.toNat - 1)))) p n i
      (j - 1#32) key := by
  obtain ⟨ys, hlen, hperm, hsort, h1, hi, hkey, hj, hso, hw, hgts⟩ := hin
  obtain ⟨hb, hw32⟩ := hp
  have hj1 : 1 ≤ j.toNat := by
    rcases Nat.eq_zero_or_pos j.toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hj0
    · exact h0
  have hi' : i.toNat < ys.length := by omega
  have hjb : p.toNat + 4 * j.toNat + 4 ≤ M15.size := by rw [hso.1]; omega
  have hprev : wd M15 (p.toNat + 4 * (j.toNat - 1)) = ys[j.toNat - 1] := by
    rw [← getElem_hole_pred hj1 hj hi']
    have := getElem_words (B := M15) (p := p.toNat) (k := j.toNat - 1) (n := n.toNat) (by omega)
    simp only [hw] at this
    exact this.symm
  refine ⟨ys, hlen, hperm, hsort, h1, hi, hkey, by rw [toNat_pred hj0]; omega,
    hso.trans (sameOutside_wr _ hjb (by omega) (by omega)), ?_, ?_⟩
  · rw [words_wr _ (by omega) (by rw [hso.1]; omega), hw, hprev, toNat_pred hj0]
    exact hole_shift hj1 hj hi'
  · show ∀ x ∈ (ys.take i.toNat).drop (j - 1#32).toNat, key.toInt < x.toInt
    rw [toNat_pred hj0]
    intro x hx
    have hd : (ys.take i.toNat).drop (j.toNat - 1) =
        ys[j.toNat - 1] :: (ys.take i.toNat).drop j.toNat := by
      rw [List.drop_eq_getElem_cons (by simp; omega), List.getElem_take]
      congr 2
      omega
    rw [hd] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [← hprev]
      omega
    · exact hgts x hx

theorem c_shift {M16 M15 M8 M0 : ByteArray} {p n i j key j' : BitVec 32}
    (h : j' = j - 1#32 ∧
      M16 = stW 32 4 M15 ((p + j * 4#32).toNat + 0)
        (ldW 32 4 .unsigned M15 ((p + (j - 1#32) * 4#32).toNat + 0)) ∧
      ¬(ldW 32 4 .unsigned M15 ((p + (j - 1#32) * 4#32).toNat + 0)).toInt ≤ key.toInt ∧
      j ≠ 0#32 ∧ sortFns.pr2 2 M15 M0 [p, n, i, j, key] ∧
      key = ldW 32 4 .unsigned M8 ((p + i * 4#32).toNat + 0) ∧ ¬n.toNat ≤ i.toNat ∧
      sortFns.pr2 1 M8 M0 [p, n, i] ∧ sortFns.pr 0 M0 [p, n]) :
    sortFns.pr2 2 M16 M0 [p, n, i, j', key] := by
  obtain ⟨rfl, rfl, hgt, hj0, hin, -, -, -, hp⟩ := h
  have hb := in_bound hin hp
  have hjn : j.toNat < n.toNat := in_lt hin
  have ha : (p + j * 4#32).toNat = p.toNat + 4 * j.toNat := by
    have := hp.2; exact addr_toNat (by omega)
  have ha' : (p + (j - 1#32) * 4#32).toNat = p.toNat + 4 * (j.toNat - 1) := by
    have := hp.2; rw [addr_toNat (by rw [toNat_pred hj0]; omega), toNat_pred hj0]
  rw [Nat.add_zero, ldW_wd, ha'] at hgt ⊢
  rw [stW_wr _ hb, ha]
  exact shift hin hp hj0 hgt

end Silmaril.Wasm.Auto2.VCSort

namespace Silmaril.Wasm.Auto2.VCSort

open Silmaril.Wasm.Auto2.VCGen

/-- Close one condition of `insertion_sort` (see `sort_vcs`). -/
macro "sort_vc" : tactic => `(tactic| (
  intro h
  first
    | exact c_entry h
    | exact c_exit h
    | exact c_key_bound h
    | exact c_inner_entry h
    | exact c_place0 h
    | exact c_place h
    | exact c_shift h
    | (cases_type* And
       first
        | exact in_bound (sortFns_in.mp ‹_›) (sortFns_pre.mp ‹_›)
        | exact in_bound_pred (sortFns_in.mp ‹_›) (sortFns_pre.mp ‹_›) ‹_›
        | bv_omega)))

set_option maxRecDepth 100000 in
/-- **The conditions of `insertion_sort`** against `sortSpecV` (15, total correctness). -/
theorem sort_vcs :
    AllValid sortFns (genFunc sortSpecV Silmaril.WasmSpec.InsertionSort.sortFunc sortFuel) := by
  vcgen4
  all_goals sort_vc

end Silmaril.Wasm.Auto2.VCSort
