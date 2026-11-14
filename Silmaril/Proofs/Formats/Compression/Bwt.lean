module

public import Silmaril.Formats.Compression.Bwt.Defs

/-! Proofs for `Silmaril.Formats.Compression.Bwt.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Bwt

open Silmaril.Formats.Compression.Bwt

/-! ## Insertion sort -/

section Sorting

variable {β : Type} (le : β → β → Bool)

theorem insertSorted_perm (a : β) : ∀ l : List β, (insertSorted le a l).Perm (a :: l)
  | [] => .refl _
  | b :: l => by
    unfold insertSorted
    split
    · exact .refl _
    · exact ((insertSorted_perm a l).cons b).trans (.swap a b l)

theorem insertionSort_perm : ∀ l : List β, (insertionSort le l).Perm l
  | [] => .refl _
  | a :: l => (insertSorted_perm le a _).trans ((insertionSort_perm l).cons a)

variable {le}

theorem pairwise_insertSorted (total : ∀ a b, le a b || le b a)
    (trans : ∀ a b c, le a b → le b c → le a c) (a : β) :
    ∀ l : List β, l.Pairwise (le · ·) → (insertSorted le a l).Pairwise (le · ·)
  | [] , _ => List.pairwise_singleton _ _
  | b :: l, h => by
    unfold insertSorted
    rw [List.pairwise_cons] at h
    split
    · next hab =>
      refine List.Pairwise.cons ?_ (List.Pairwise.cons h.1 h.2)
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab
      · exact trans _ _ _ hab (h.1 x hx)
    · next hab =>
      have hba : le b a := by have := total a b; simp_all
      refine List.Pairwise.cons ?_ (pairwise_insertSorted total trans a l h.2)
      intro x hx
      rcases List.mem_cons.mp ((insertSorted_perm le a l).subset hx) with rfl | hx
      · exact hba
      · exact h.1 x hx

theorem pairwise_insertionSort (total : ∀ a b, le a b || le b a)
    (trans : ∀ a b c, le a b → le b c → le a c) :
    ∀ l : List β, (insertionSort le l).Pairwise (le · ·)
  | [] => .nil
  | a :: l => pairwise_insertSorted total trans a _ (pairwise_insertionSort total trans l)

end Sorting

/-! ## Lexicographic order on rows -/

section Lex

variable {α : Type} [LT α]

theorem lt_append_of_lt {x y : List α} (hl : x.length = y.length) (h : x < y) (u v : List α) :
    x ++ u < y ++ v := by
  induction h with
  | nil => simp at hl
  | rel h => exact .rel h
  | cons _ ih => exact .cons (ih (by simpa using hl))

/-- Rows of equal length that end in the same symbol compare like their prefixes. -/
theorem le_of_append_le [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] {x y : List α}
    (hl : x.length = y.length) {u v : List α}
    (h : x ++ u ≤ y ++ v) : x ≤ y :=
  fun hyx => h (lt_append_of_lt hl.symm hyx v u)

theorem cons_le_cons_of_le [LE α] [Std.IsPreorder α] [Std.LawfulOrderLT α] {x y : List α}
    (c : α) (h : x ≤ y) : c :: x ≤ c :: y := by
  intro hlt
  cases hlt with
  | rel h' => exact Std.lt_irrefl h'
  | cons h' => exact h h'

end Lex

/-! ## Rotations -/

section Rotations

variable {α : Type}

/-- Rotate right by one. -/
def rotr (r : List α) : List α := r.getLast?.toList ++ r.dropLast

theorem rotr_concat (x : List α) (c : α) : rotr (x ++ [c]) = c :: x := by
  simp [rotr]

theorem rotl_rotr (r : List α) : rotl (rotr r) = r := by
  rcases List.eq_nil_or_concat r with rfl | ⟨x, c, rfl⟩
  all_goals try rw [List.concat_eq_append]
  · rfl
  · rw [rotr_concat]; rfl

theorem rotr_rotl : ∀ r : List α, rotr (rotl r) = r
  | [] => rfl
  | a :: l => rotr_concat l a

theorem lastD_concat [Inhabited α] (x : List α) (c : α) : lastD (x ++ [c]) = c := by
  simp [lastD]

theorem lastD_eq_headD_rotr [Inhabited α] (r : List α) : lastD r = (rotr r).headD default := by
  rcases List.eq_nil_or_concat r with rfl | ⟨x, c, rfl⟩
  all_goals try rw [List.concat_eq_append]
  · rfl
  · rw [rotr_concat, lastD_concat]; rfl

variable (s : List α)

theorem length_rotation {k : Nat} (hk : k ≤ s.length) : (rotation s k).length = s.length := by
  simp [rotation]; omega

theorem rotation_zero : rotation s 0 = s := by simp [rotation]

theorem rotation_length : rotation s s.length = s := by simp [rotation]

theorem rotation_succ {k : Nat} (hk : k < s.length) :
    rotation s (k + 1) = (s.drop (k + 1) ++ s.take k) ++ [s[k]] := by
  rw [rotation, List.take_add_one, List.getElem?_eq_getElem hk]; simp

theorem rotl_rotation {k : Nat} (hk : k < s.length) :
    rotl (rotation s k) = rotation s (k + 1) := by
  rw [rotation_succ s hk, rotation, List.drop_eq_getElem_cons hk, List.cons_append, rotl]

theorem lastD_rotation_succ [Inhabited α] {k : Nat} (hk : k < s.length) :
    lastD (rotation s (k + 1)) = s[k] := by
  rw [rotation_succ s hk, lastD_concat]

theorem headD_rotation [Inhabited α] {k : Nat} (hk : k < s.length) :
    (rotation s k).headD default = s[k] := by
  rw [rotation, List.drop_eq_getElem_cons hk]; rfl

theorem length_rotations : (rotations s).length = s.length := by simp [rotations]

theorem mem_rotations_length {r : List α} (h : r ∈ rotations s) : r.length = s.length := by
  simp only [rotations, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact length_rotation s (Nat.le_of_lt hk)

theorem map_rotl_rotations : ((rotations s).map rotl).Perm (rotations s) := by
  rcases h : s.length with _ | m
  · simp [rotations, h]
  · have e : (rotations s).map rotl =
        (List.range m).map (fun k => rotation s (k + 1)) ++ [rotation s 0] := by
      rw [rotations, h, List.range_succ, List.map_map, List.map_append]
      congr 1
      · refine List.map_congr_left fun k hk => ?_
        simp only [Function.comp, List.mem_range] at hk ⊢
        exact rotl_rotation s (by omega)
      · simp only [List.map_cons, List.map_nil, Function.comp]
        rw [rotl_rotation s (by omega), ← h, rotation_length, rotation_zero]
    rw [e, rotations, h, List.range_succ_eq_map, List.map_cons, List.map_map]
    exact List.perm_append_singleton _ _

theorem map_rotr_rotations : ((rotations s).map rotr).Perm (rotations s) := by
  have := (map_rotl_rotations s).map rotr
  rw [List.map_map] at this
  simp only [Function.comp_def, rotr_rotl, List.map_id'] at this
  exact this.symm

theorem map_headD_rotations [Inhabited α] : (rotations s).map (·.headD default) = s := by
  refine List.ext_getElem (by simp [rotations]) fun k h₁ h₂ => ?_
  simp only [rotations, List.getElem_map, List.getElem_range]
  exact headD_rotation s h₂

theorem map_lastD_rotations_perm [Inhabited α] : ((rotations s).map lastD).Perm s := by
  have := (map_rotr_rotations s).map (·.headD default)
  rw [List.map_map, map_headD_rotations] at this
  simpa only [Function.comp_def, ← lastD_eq_headD_rotr] using this

end Rotations

/-! ## The sorted matrix and the LF table -/

section Matrix

variable {α : Type} [LT α] [DecidableEq α] [DecidableLT α]

theorem sortedRotations_perm (s : List α) : (sortedRotations s).Perm (rotations s) :=
  insertionSort_perm _ _

theorem length_sortedRotations (s : List α) : (sortedRotations s).length = s.length :=
  (sortedRotations_perm s).length_eq.trans (length_rotations s)

theorem mem_sortedRotations_length {s r : List α} (h : r ∈ sortedRotations s) :
    r.length = s.length :=
  mem_rotations_length s ((sortedRotations_perm s).subset h)

theorem getD_eq_getElem' {β : Type} (l : List β) (d : β) {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

variable [Inhabited α]

theorem succTable_perm (L : List α) : (succTable L).Perm (List.range L.length) :=
  insertionSort_perm _ _

variable [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]

omit [Inhabited α] in
theorem sortedRotations_pairwise (s : List α) : (sortedRotations s).Pairwise (· ≤ ·) := by
  have := pairwise_insertionSort (le := fun a b : List α => decide (a ≤ b))
    (fun a b => by simpa using List.le_total a b)
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact List.le_trans hab hbc)
    (rotations s)
  simpa [sortedRotations] using this

theorem lastColumnLe_total (L : List α) (i j : Nat) :
    lastColumnLe L i j || lastColumnLe L j i := by
  simp only [lastColumnLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases Std.lt_trichotomy (L.getD i default) (L.getD j default) with h | h | h
  · exact .inl (.inl h)
  · rw [h]; rcases Nat.le_total i j with h' | h'
    · exact .inl (.inr ⟨rfl, h'⟩)
    · exact .inr (.inr ⟨rfl, h'⟩)
  · exact .inr (.inl h)

theorem lastColumnLe_trans (L : List α) (i j k : Nat) (hij : lastColumnLe L i j)
    (hjk : lastColumnLe L j k) : lastColumnLe L i k := by
  simp only [lastColumnLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  rcases hij with hij | ⟨hij, hij'⟩ <;> rcases hjk with hjk | ⟨hjk, hjk'⟩
  · exact .inl (Std.lt_trans hij hjk)
  · exact .inl (hjk ▸ hij)
  · exact .inl (hij ▸ hjk)
  · exact .inr ⟨hij.trans hjk, Nat.le_trans hij' hjk'⟩

theorem succTable_pairwise (L : List α) :
    (succTable L).Pairwise (lastColumnLe L · ·) :=
  pairwise_insertionSort (lastColumnLe_total L)
    (fun a b c hab hbc => lastColumnLe_trans L a b c hab hbc) _

/-- Two rows in matrix order, rotated right by one, stay in order when their last
symbols are in order, or equal: the heart of the LF mapping. -/
theorem rotr_le_rotr {s : List α} {i j : Nat} (hi : i < s.length) (hj : j < s.length)
    (h : lastColumnLe ((sortedRotations s).map lastD) i j) :
    rotr ((sortedRotations s).getD i []) ≤ rotr ((sortedRotations s).getD j []) := by
  have hn := length_sortedRotations s
  have hi' : i < (sortedRotations s).length := hn ▸ hi
  have hj' : j < (sortedRotations s).length := hn ▸ hj
  rw [getD_eq_getElem' _ _ hi', getD_eq_getElem' _ _ hj']
  simp only [lastColumnLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    getD_eq_getElem' _ _ (by simpa using hi' : i < ((sortedRotations s).map lastD).length),
    getD_eq_getElem' _ _ (by simpa using hj' : j < ((sortedRotations s).map lastD).length),
    List.getElem_map] at h
  have li := mem_sortedRotations_length (List.getElem_mem hi')
  have lj := mem_sortedRotations_length (List.getElem_mem hj')
  have hle : i ≤ j → (sortedRotations s)[i] ≤ (sortedRotations s)[j] := fun hij => by
    rcases Nat.lt_or_eq_of_le hij with hij | rfl
    · exact List.pairwise_iff_getElem.mp (sortedRotations_pairwise s) i j hi' hj' hij
    · exact List.le_refl _
  generalize (sortedRotations s)[i] = ri at h li hle
  generalize (sortedRotations s)[j] = rj at h lj hle
  rcases List.eq_nil_or_concat ri with rfl | ⟨x, c, rfl⟩
  · simp at li; omega
  rcases List.eq_nil_or_concat rj with rfl | ⟨y, d, rfl⟩
  · simp at lj; omega
  simp only [List.concat_eq_append, lastD_concat, List.length_append] at *
  rw [rotr_concat, rotr_concat]
  rcases h with h | ⟨rfl, hij⟩
  · exact List.le_of_lt (.rel h)
  · exact cons_le_cons_of_le c (le_of_append_le (by simp at li lj; omega) (hle hij))

/-- **The LF mapping.** The rows of the matrix, taken in the order of the LF table and
rotated right by one, are the matrix again. Both sides are sorted (`rotr_le_rotr`)
and permutations of the rotations (`map_rotr_rotations`), so they are equal. -/
theorem map_succTable (s : List α) :
    (succTable ((sortedRotations s).map lastD)).map
      (fun k => rotr ((sortedRotations s).getD k [])) = sortedRotations s := by
  have hL : ((sortedRotations s).map lastD).length = s.length := by
    simp [length_sortedRotations]
  have hT := succTable_perm ((sortedRotations s).map lastD)
  rw [hL] at hT
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · intro a b _ _ h1 h2; exact Std.le_antisymm h1 h2
  · rw [List.pairwise_map]
    refine (succTable_pairwise _).imp_of_mem ?_
    intro i j hi hj h
    exact rotr_le_rotr (by simpa using hT.subset hi) (by simpa using hT.subset hj) h
  · exact sortedRotations_pairwise s
  · refine (hT.map _).trans ?_
    have e : (List.range s.length).map (fun k => rotr ((sortedRotations s).getD k [])) =
        (sortedRotations s).map rotr := by
      refine List.ext_getElem (by simp [length_sortedRotations]) fun k h1 h2 => ?_
      simp only [List.getElem_map, List.getElem_range]
      rw [getD_eq_getElem' _ _ (by simpa using h2)]
    rw [e]
    exact (((sortedRotations_perm s).map rotr).trans (map_rotr_rotations s)).trans
      (sortedRotations_perm s).symm

omit [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] in
theorem succTable_lt {L : List α} {i : Nat} (hi : i < L.length) :
    (succTable L).getD i 0 < L.length := by
  have hT := succTable_perm L
  have hi' : i < (succTable L).length := by simpa [hT.length_eq] using hi
  rw [getD_eq_getElem' _ _ hi']
  simpa using hT.subset (List.getElem_mem hi')

/-- Following the LF table from row `i` reaches the rotation of row `i` by one to the
left. -/
theorem getD_sortedRotations_succTable {s : List α} {i : Nat} (hi : i < s.length) :
    (sortedRotations s).getD ((succTable ((sortedRotations s).map lastD)).getD i 0) [] =
      rotl ((sortedRotations s).getD i []) := by
  have e := congrArg (fun l => rotl (l.getD i [])) (map_succTable s)
  have hT := (succTable_perm ((sortedRotations s).map lastD)).length_eq
  simp only [List.length_map, List.length_range, length_sortedRotations] at hT
  rw [getD_eq_getElem' _ 0 (by omega : i < (succTable ((sortedRotations s).map lastD)).length)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (hT ▸ hi : i < _), Option.map_some, Option.getD_some,
    rotl_rotr] at e
  simpa [List.getD_eq_getElem?_getD] using e

end Matrix

/-! ## The inverse -/

section Inverse

variable {α : Type} [LT α] [LE α] [DecidableEq α] [DecidableLT α] [Inhabited α]
  [Std.IsLinearOrder α] [Std.LawfulOrderLT α]

theorem ibwtWalk_eq (s : List α) :
    ∀ (fuel j i : Nat), j + fuel ≤ s.length → i < s.length →
      (sortedRotations s).getD i [] = rotation s j →
      ibwtWalk ((sortedRotations s).map lastD) (succTable ((sortedRotations s).map lastD))
        i fuel = (s.drop j).take fuel
  | 0, _, _, _, _, _ => by simp [ibwtWalk]
  | fuel + 1, j, i, hf, hi, hrow => by
    have hj : j < s.length := by omega
    have hL : ((sortedRotations s).map lastD).length = s.length := by
      simp [length_sortedRotations]
    have ht := succTable_lt (hL ▸ hi : i < ((sortedRotations s).map lastD).length)
    rw [hL] at ht
    have hrow' := getD_sortedRotations_succTable hi
    rw [hrow, rotl_rotation s hj] at hrow'
    simp only [ibwtWalk]
    rw [ibwtWalk_eq s fuel (j + 1) _ (by omega) ht hrow',
      List.drop_eq_getElem_cons hj, List.take_succ_cons]
    congr 1
    rw [getD_eq_getElem' _ _ (by simpa [length_sortedRotations] using ht), List.getElem_map,
      ← getD_eq_getElem' _ _ (by simpa [length_sortedRotations] using ht), hrow',
      lastD_rotation_succ s hj]

omit [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] in
theorem bwt_fst_length (s : List α) : (bwt s).1.length = s.length := by
  simp [bwt, length_sortedRotations]

omit [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] in
theorem bwt_fst_perm (s : List α) : (bwt s).1.Perm s :=
  ((sortedRotations_perm s).map lastD).trans (map_lastD_rotations_perm s)

omit [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] in
theorem bwt_snd_spec {s : List α} (h : 0 < s.length) :
    (bwt s).2 < s.length ∧ (sortedRotations s).getD (bwt s).2 [] = s := by
  have hmem : s ∈ sortedRotations s := (sortedRotations_perm s).symm.subset (by
    simp only [rotations, List.mem_map, List.mem_range]
    exact ⟨0, h, rotation_zero s⟩)
  have hlt := List.findIdx_lt_length_of_exists (p := fun r => decide (r = s)) ⟨s, hmem, by simp⟩
  have hget := List.findIdx_getElem (w := hlt)
  simp only [decide_eq_true_eq] at hget
  refine ⟨by simpa [bwt, length_sortedRotations] using hlt, ?_⟩
  simp only [bwt]
  rw [getD_eq_getElem' _ _ hlt, hget]

/-- **Main theorem**: the inverse Burrows–Wheeler transform recovers the input. -/
theorem ibwt_bwt (s : List α) : ibwt (bwt s) = s := by
  rcases Nat.eq_zero_or_pos s.length with h | h
  · simp [ibwt, bwt_fst_length, ibwtWalk, List.eq_nil_of_length_eq_zero h]
  · obtain ⟨hlt, hrow⟩ := bwt_snd_spec h
    rw [ibwt, bwt_fst_length]
    have := ibwtWalk_eq s s.length 0 (bwt s).2 (by omega) hlt (hrow.trans (rotation_zero s).symm)
    simpa [bwt] using this

end Inverse


/-! ## Move-to-front -/

theorem mem_mtfInit (b : UInt8) : b ∈ mtfInit := by
  simp only [mtfInit, List.mem_map, List.mem_range]
  exact ⟨b.toNat, b.toNat_lt, UInt8.ofNat_toNat⟩

theorem length_mtfInit : mtfInit.length = 256 := by simp [mtfInit]

theorem mtfDecodeWith_mtfEncodeWith :
    ∀ (s tbl : List UInt8), (∀ b, b ∈ tbl) → mtfDecodeWith tbl (mtfEncodeWith tbl s) = s
  | [], _, _ => rfl
  | b :: s, tbl, h => by
    have hlt := List.idxOf_lt_length_of_mem (h b)
    have hb : tbl.getD (tbl.idxOf b) 0 = b := by
      rw [getD_eq_getElem' _ _ hlt, List.getElem_idxOf hlt]
    simp only [mtfEncodeWith, mtfDecodeWith, hb, ← List.erase_eq_eraseIdx_of_idxOf rfl]
    refine congrArg _ (mtfDecodeWith_mtfEncodeWith s _ fun c => ?_)
    by_cases hc : c = b
    · exact hc ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hc).mpr (h c))

theorem mtfEncodeWith_lt :
    ∀ (s tbl : List UInt8), (∀ b, b ∈ tbl) → ∀ i ∈ mtfEncodeWith tbl s, i < tbl.length
  | [], _, _, _, hi => by simp [mtfEncodeWith] at hi
  | b :: s, tbl, h, i, hi => by
    simp only [mtfEncodeWith, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact List.idxOf_lt_length_of_mem (h b)
    · have hmem : ∀ c, c ∈ b :: tbl.erase b := fun c => by
        by_cases hc : c = b
        · exact hc ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hc).mpr (h c))
      have h1 := mtfEncodeWith_lt s _ hmem i hi
      have h2 := List.length_erase_of_mem (h b)
      have h3 := List.length_pos_of_mem (h b)
      simp only [List.length_cons] at h1
      omega

/-! ## Zero-run coding -/

theorem runDigitsAux_spec :
    ∀ (fuel r : Nat), r ≤ fuel →
      runValue (runDigitsAux fuel r) = r ∧ ∀ d ∈ runDigitsAux fuel r, d ≤ runB
  | 0, r, h => by simp [runDigitsAux, runValue]; omega
  | fuel + 1, r, h => by
    simp only [runDigitsAux]
    split
    · simp [runValue, *]
    split
    · obtain ⟨h1, h2⟩ := runDigitsAux_spec fuel (r / 2) (by omega)
      simp only [runValue, List.mem_cons, forall_eq_or_imp, runA, runB]
      exact ⟨by omega, by omega, h2⟩
    · obtain ⟨h1, h2⟩ := runDigitsAux_spec fuel (r / 2 - 1) (by omega)
      simp only [runValue, List.mem_cons, forall_eq_or_imp, runB]
      exact ⟨by omega, by omega, h2⟩

theorem runValue_runDigits (r : Nat) : runValue (runDigits r) = r :=
  (runDigitsAux_spec r r (Nat.le_refl r)).1

theorem runDigits_le (r : Nat) : ∀ d ∈ runDigits r, d ≤ runB :=
  (runDigitsAux_spec r r (Nat.le_refl r)).2

theorem zrleDecodeAux_append :
    ∀ (ds ds' l : List Nat), (∀ d ∈ ds', d ≤ runB) →
      zrleDecodeAux ds (ds' ++ l) = zrleDecodeAux (ds ++ ds') l
  | ds, [], l, _ => by simp
  | ds, d :: ds', l, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [List.cons_append, zrleDecodeAux, h.1, ↓reduceIte]
    rw [zrleDecodeAux_append _ ds' l h.2, List.append_assoc, List.singleton_append]

theorem zrleDecode_zrleEncodeAux :
    ∀ (z : Nat) (l : List Nat), zrleDecode (zrleEncodeAux z l) = List.replicate z 0 ++ l
  | z, [] => by
    rw [zrleEncodeAux, zrleDecode, ← List.append_nil (runDigits z),
      zrleDecodeAux_append _ _ _ (runDigits_le z)]
    simp [zrleDecodeAux, runValue_runDigits]
  | z, 0 :: l => by
    rw [zrleEncodeAux, zrleDecode_zrleEncodeAux (z + 1) l, List.replicate_succ',
      List.append_assoc, List.singleton_append]
  | z, (v + 1) :: l => by
    rw [zrleEncodeAux, zrleDecode, zrleDecodeAux_append _ _ _ (runDigits_le z)]
    simp only [List.nil_append, zrleDecodeAux, runValue_runDigits]
    rw [ite_eq_right (by simp only [runB]; omega)]
    have := zrleDecode_zrleEncodeAux 0 l
    simp only [zrleDecode, List.replicate_zero, List.nil_append] at this
    simp [this]

end Silmaril.Proofs.Formats.Compression.Bwt
