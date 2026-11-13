module

public import Silmaril.Wasm.Auto2.VCBSearch.Defs
public import Silmaril.Wasm.Logic.Words.Thms

/-!
# `btree_search` through the VC generator: facts about trees

Facts about the library's trees used by the conditions of `btree_search`: the parts of a page
that represents a tree (`repr_parts`), that bounded arrays are determined by memory
(`ba_unique`), that a key of an ordered tree lies within its bounds (`inTree_within`), the key
`k` is in the child the search descends to iff it is in the node (`inTree_child`), and the ghost
height (`hgt_le`, `hgt_spec`, `hgt_child`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCBSearch

open Silmaril.Wasm
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.BTree (OBA OBAnd BA FindsAt Tree Repr Ordered Within InTree IsBTree page
  int32Max)

/-! ## Pages -/

/-- The parts of a page that represents a tree. -/
theorem repr_parts {B : ByteArray} {x : Nat} {T : Tree} (h : Repr B x T) :
    ∃ l ks cs, T = .node l ks cs ∧ OBAnd B (page * x + 4) 8090 ks ∧
      (l = true ↔ wd B (page * x) ≠ 0) ∧ (l = true → cs = []) ∧
      (l = false → ∃ ps, BA B (page * x + 32768) 8091 ps ∧ ps.length = cs.length ∧
        ∀ i (h₁ : i < ps.length) (h₂ : i < cs.length), Repr B ps[i].toNat cs[i]) := by
  cases h with
  | leaf hl hk =>
    exact ⟨true, _, [], rfl, hk, ⟨fun _ => hl, fun _ => rfl⟩, fun _ => rfl, (fun h => nomatch h)⟩
  | inner hl hk hp hlen hc =>
    refine ⟨false, _, _, rfl, hk, ⟨(fun h => nomatch h), fun h => absurd hl h⟩, (fun h => nomatch h), ?_⟩
    · intro _
      exact ⟨_, hp, hlen, hc⟩

/-- A bounded array is determined by memory. -/
theorem ba_unique {B : ByteArray} {x n n' : Nat} {α α' : List (BitVec 32)} (h : BA B x n α)
    (h' : BA B x n' α') : α = α' := by
  obtain ⟨hl, hw, hn, hx, -⟩ := h
  obtain ⟨hl', hw', hn', hx', -⟩ := h'
  simp only [int32Max] at hx hx'
  have hlen : α.length = α'.length := by
    have h₁ := congrArg BitVec.toNat (hl.symm.trans hl')
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h₁
    exact h₁
  rw [← hw, ← hw', hlen]

/-- The page of a node does not wrap: `page * x + 4 + 4 * 8090 < 2 ^ 31`. -/
theorem page_bound {B : ByteArray} {x : Nat} {ks : List (BitVec 32)}
    (h : OBAnd B (page * x + 4) 8090 ks) : page * x + 4 + 4 + 4 * 8090 ≤ int32Max ∧
      page * x + 4 + 4 + 4 * 8090 ≤ B.size :=
  ⟨h.1.1.2.2.2.1, h.1.1.2.2.2.2⟩

/-- The length word of an ordered bounded array. -/
theorem oba_len {B : ByteArray} {x n : Nat} {α : List (BitVec 32)} (h : OBA B x n α) :
    (wd B x).toNat = α.length := by
  obtain ⟨⟨hl, -, hn, hx, -⟩, -⟩ := h
  simp only [int32Max] at hx
  rw [hl, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## Ordered trees -/

/-- The bound of child `i` of a node with keys `ks` and bounds `lo`, `hi`. -/
abbrev loOf (lo : Option (BitVec 32)) (ks : List (BitVec 32)) (i : Nat) : Option (BitVec 32) :=
  if i = 0 then lo else ks[i - 1]?

abbrev hiOf (hi : Option (BitVec 32)) (ks : List (BitVec 32)) (i : Nat) : Option (BitVec 32) :=
  if i = ks.length then hi else ks[i]?

/-- A child's bounds are within its node's. -/
theorem within_child {lo hi : Option (BitVec 32)} {ks : List (BitVec 32)} {i : Nat} {k : BitVec 32}
    (hw : ∀ k ∈ ks, Within lo hi k) (hi' : i ≤ ks.length)
    (h : Within (loOf lo ks i) (hiOf hi ks i) k) : Within lo hi k := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨fun l hl => ?_, fun u hu => ?_⟩
  · by_cases hi0 : i = 0
    · exact h₁ l (by simp [loOf, hi0, hl])
    · have hm : ks[i - 1]'(by omega) ∈ ks := List.getElem_mem _
      have := (hw _ hm).1 l hl
      have := h₁ (ks[i - 1]'(by omega)) (by simp [loOf, hi0, List.getElem?_eq_getElem (show i - 1 <
        ks.length by omega)])
      omega
  · by_cases hil : i = ks.length
    · exact h₂ u (by simp [hiOf, hil, hu])
    · have hm : ks[i]'(by omega) ∈ ks := List.getElem_mem _
      have := (hw _ hm).2 u hu
      have := h₂ (ks[i]'(by omega)) (by simp [hiOf, hil, List.getElem?_eq_getElem (show i <
        ks.length by omega)])
      omega

/-- The child step of `inTree_within`: a key of child `j` lies within the node's bounds. -/
theorem within_of_child {B : ByteArray} {x : Nat} {lo hi : Option (BitVec 32)} {l : Bool}
    {ks : List (BitVec 32)} {cs : List Tree} {k : BitVec 32} {j : Nat} (hj : j < cs.length)
    (hr : Repr B x (.node l ks cs)) (ho : Ordered lo hi (.node l ks cs))
    (ih : ∀ {x : Nat} {lo hi : Option (BitVec 32)}, Repr B x cs[j] → Ordered lo hi cs[j] →
      Within lo hi k) : Within lo hi k := by
  obtain ⟨l', ks', cs', he, -, -, hleaf, hinner⟩ := repr_parts hr
  simp only [Tree.node.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  cases l with
  | true => simp [hleaf rfl] at hj
  | false =>
    obtain ⟨ps, -, hpl, hpr⟩ := hinner rfl
    cases ho with
    | mk hs hw hlen hch =>
      have hlen' : cs.length = ks.length + 1 := hlen rfl
      exact within_child hw (by omega) (ih (hpr j (by omega) hj) (hch j hj))

/-- **A key of an ordered tree that a page represents lies within its bounds.** -/
theorem inTree_within {B : ByteArray} {k : BitVec 32} {T : Tree} (h : InTree k T) :
    ∀ {x : Nat} {lo hi : Option (BitVec 32)}, Repr B x T → Ordered lo hi T → Within lo hi k := by
  induction h with
  | here hk =>
    intro x lo hi _ ho
    cases ho with
    | mk _ hw _ _ => exact hw _ hk
  | child hc _ ih =>
    intro x lo hi hr ho
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    exact within_of_child hj hr ho ih

/-! ## The descent -/

theorem getD_eq {ks : List (BitVec 32)} {j : Nat} (h : j < ks.length) : ks.getD j 0 = ks[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The key `k` is not among the keys if the found index does not hold it. -/
theorem notin_keys {ks : List (BitVec 32)} {k : BitVec 32} {i : Nat}
    (hs : ks.Pairwise fun a b => a.toInt < b.toInt) (hf : FindsAt ks k i)
    (hne : i < ks.length → ks.getD i 0 ≠ k) : k ∉ ks := by
  intro hk
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hk
  obtain ⟨hi, hlt, hge⟩ := hf
  rcases Nat.lt_trichotomy j i with hji | rfl | hji
  · have := hlt j hji
    rw [getD_eq hj] at this
    omega
  · exact hne hj (getD_eq hj)
  · have h₁ := hge i (le_refl _) (by omega)
    have h₂ := List.pairwise_iff_getElem.mp hs i j (by omega) hj hji
    rw [getD_eq (by omega)] at h₁
    omega

/-- The bounds of the child the search descends to contain `k`. -/
theorem within_found {lo hi : Option (BitVec 32)} {ks : List (BitVec 32)} {k : BitVec 32} {i : Nat}
    (hw : Within lo hi k) (hf : FindsAt ks k i) (hne : i < ks.length → ks.getD i 0 ≠ k) :
    Within (loOf lo ks i) (hiOf hi ks i) k := by
  obtain ⟨hi, hlt, hge⟩ := hf
  refine ⟨fun l hl => ?_, fun u hu => ?_⟩
  · by_cases hi0 : i = 0
    · exact hw.1 l (by simpa [loOf, hi0] using hl)
    · have hl' : ks[i - 1]'(by omega) = l := by
        simpa [loOf, hi0, List.getElem?_eq_getElem (show i - 1 < ks.length by omega)] using hl
      have := hlt (i - 1) (by omega)
      rw [getD_eq (by omega), hl'] at this
      exact this
  · by_cases hil : i = ks.length
    · exact hw.2 u (by simpa [hiOf, hil] using hu)
    · have hu' : ks[i]'(by omega) = u := by
        simpa [hiOf, hil, List.getElem?_eq_getElem (show i < ks.length by omega)] using hu
      have h₁ := hge i (le_refl _) (by omega)
      have h₂ := hne (by omega)
      rw [getD_eq (by omega), hu'] at h₁ h₂
      have : k.toInt ≠ u.toInt := fun h => h₂ (BitVec.eq_of_toInt_eq h).symm
      omega

/-- The child pointers of an inner node. -/
theorem inner_ptrs {B : ByteArray} {x : Nat} {ks : List (BitVec 32)} {cs : List Tree}
    (hr : Repr B x (.node false ks cs)) :
    ∃ ps, BA B (page * x + 32768) 8091 ps ∧ ps.length = cs.length ∧
      ∀ i (h₁ : i < ps.length) (h₂ : i < cs.length), Repr B ps[i].toNat cs[i] := by
  obtain ⟨l', ks', cs', he, -, -, -, hinner⟩ := repr_parts hr
  simp only [Tree.node.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact hinner rfl

/-- A key of child `j ≠ i` of the node is not `k`, the key the search looks for at child `i`. -/
theorem not_other_child {lo hi : Option (BitVec 32)} {ks : List (BitVec 32)} {k : BitVec 32}
    {i j : Nat} (hf : FindsAt ks k i) (hcl : j < ks.length + 1) (hji : j ≠ i)
    (hwj : Within (loOf lo ks j) (hiOf hi ks j) k) : False := by
  obtain ⟨hik, hlt, hge⟩ := hf
  rcases Nat.lt_or_gt_of_ne hji with hji | hji
  · have h₁ := hwj.2 (ks[j]'(by omega)) (by
      simp [hiOf, show j ≠ ks.length by omega, List.getElem?_eq_getElem (show j < ks.length by omega)])
    have h₂ := hlt j hji
    rw [getD_eq (by omega)] at h₂
    omega
  · have h₁ := hwj.1 (ks[j - 1]'(by omega)) (by
      simp [loOf, show j ≠ 0 by omega, List.getElem?_eq_getElem (show j - 1 < ks.length by omega)])
    have h₂ := hge (j - 1) (by omega) (by omega)
    rw [getD_eq (by omega)] at h₂
    omega

/-- **The key is in the node iff it is in the child the search descends to.** -/
theorem inTree_child {B : ByteArray} {x : Nat} {lo hi : Option (BitVec 32)} {ks : List (BitVec 32)}
    {cs : List Tree} {k : BitVec 32} {i : Nat} (hr : Repr B x (.node false ks cs))
    (ho : Ordered lo hi (.node false ks cs)) (hf : FindsAt ks k i)
    (hne : i < ks.length → ks.getD i 0 ≠ k) :
    ∃ hi' : i < cs.length, (InTree k (.node false ks cs) ↔ InTree k cs[i]) := by
  obtain ⟨ps, -, hpl, hpr⟩ := inner_ptrs hr
  cases ho with
  | mk hs hw hlen hch =>
    have hcl : cs.length = ks.length + 1 := hlen rfl
    have hik : i ≤ ks.length := hf.1
    refine ⟨by omega, ⟨fun h => ?_, fun h => .child (List.getElem_mem _) h⟩⟩
    cases h with
    | here hk => exact absurd hk (notin_keys hs hf hne)
    | child hc hk =>
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
      by_cases hji : j = i
      · subst hji
        exact hk
      · exact (not_other_child hf (by omega) hji
          (inTree_within hk (hpr j (by omega) hj) (hch j hj))).elim

/-! ## The ghost height -/

theorem height_node (l : Bool) (ks : List (BitVec 32)) (cs : List Tree) :
    height (.node l ks cs) = heightL cs := by
  rw [height]

theorem heightL_get : ∀ (cs : List Tree) (i : Nat) (h : i < cs.length), height cs[i] < heightL cs
  | [], _, h => by simp at h
  | c :: cs, 0, _ => by
    simp only [heightL, List.getElem_cons_zero]
    omega
  | c :: cs, i + 1, h => by
    have := heightL_get cs i (by simpa using h)
    simp only [heightL, List.getElem_cons_succ]
    omega

open Classical in
theorem hgt_le {B : ByteArray} {x : Nat} {T : Tree} (h : Repr B x T) : hgt B x ≤ height T := by
  unfold hgt
  split
  · exact Nat.find_min' _ ⟨T, h, rfl⟩
  · rename_i hn
    exact absurd ⟨T, h⟩ hn

open Classical in
theorem hgt_spec {B : ByteArray} {x : Nat} {T : Tree} (h : Repr B x T) :
    ∃ T', Repr B x T' ∧ height T' = hgt B x := by
  unfold hgt
  split
  · exact Nat.find_spec (p := fun d => ∃ T, Repr B x T ∧ height T = d) _
  · rename_i hn
    exact absurd ⟨T, h⟩ hn

/-- **The child the search descends to has a smaller height.** -/
theorem hgt_child {B : ByteArray} {x : Nat} {T : Tree} {ps : List (BitVec 32)} {i : Nat}
    (hr : Repr B x T) (hleaf : wd B (page * x) = 0) (hp : BA B (page * x + 32768) 8091 ps)
    (hi : i < ps.length) : hgt B ps[i].toNat < hgt B x := by
  obtain ⟨T', hr', hh⟩ := hgt_spec hr
  obtain ⟨l, ks, cs, rfl, -, hl, -, hinner⟩ := repr_parts hr'
  have hl' : l = false := by
    cases l
    · rfl
    · exact absurd hleaf (hl.mp rfl)
  subst hl'
  obtain ⟨ps', hp', hpl, hpr⟩ := hinner rfl
  obtain rfl : ps = ps' := ba_unique hp hp'
  have h₁ := hgt_le (hpr i hi (by omega))
  have h₂ := heightL_get cs i (by omega)
  rw [height_node] at hh
  omega

end Silmaril.Wasm.Auto2.VCBSearch
