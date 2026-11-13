module

public import Silmaril.Compiler.Target.RenameCheck.Defs
public import Silmaril.Compiler.Target.QSortPerm.Defs
public import Silmaril.Compiler.Target.QSortSorted.Defs
import Init.Internal.Order.While
import Std.Data.HashSet.Lemmas

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # The sorted sets of `RegAlloc`: `ofList`, `union`, `diff`, `genKill`

`RegAlloc` keeps its live sets as strictly increasing arrays (`SSet`). This file proves
what the completeness of the renamer checker needs about them: `ofList` builds a sorted
set with the same members as its list, `union` has the members of both arguments (for
any arrays) and keeps sorted sets sorted, and `diff a b` has the members of `a` outside
`b` when both are sorted. `genKill` returns the upward-exposed uses and the definitions
of a block, so the registers live at a block's header lie in `gen ∪ (out \ kill)`.

The loops are folds (`union_eq`, `diff_eq`, `genKill_eq`); the inner `while` of `diff`
unfolds with `Lean.Loop.forIn_eq_of_monadTail` (`wloop_eq`).
-/

@[expose] public section

namespace Silmaril.Compile.Target.RegAlloc

open Silmaril.Machine Silmaril.Machine.Lir

/-- A strictly increasing array: a sorted set. -/
def SSet (a : Array Nat) : Prop := a.toList.Pairwise (· < ·)

private theorem forIn_eq_foldl_of {α β : Type} {l : List α} {init : β}
    {f : α → β → Id (ForInStep β)}
    (g : β → α → β) (h : ∀ a b, f a b = pure (.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a rest ih => rw [List.forIn_cons, h]; exact ih

private theorem SSet.lt {a : Array Nat} (ha : SSet a) {i j x y : Nat} (hx : a[i]? = some x)
    (hy : a[j]? = some y) (hij : i < j) : x < y := by
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hx
  obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.mp hy
  have := List.pairwise_iff_getElem.mp ha i j (by simpa using hi) (by simpa using hj) hij
  simpa using this

private theorem SSet.le {a : Array Nat} (ha : SSet a) {i j x y : Nat} (hx : a[i]? = some x)
    (hy : a[j]? = some y) (hij : i ≤ j) : x ≤ y := by
  rcases Nat.lt_or_eq_of_le hij with h | rfl
  · exact Nat.le_of_lt (ha.lt hx hy h)
  · rw [hx, Option.some.injEq] at hy; omega

private theorem pairwise_push {out : Array Nat} {x : Nat} (hp : out.toList.Pairwise (· < ·))
    (hlt : ∀ y ∈ out, y < x) : (out.push x).toList.Pairwise (· < ·) := by
  simp only [Array.toList_push, List.pairwise_append, List.pairwise_singleton, List.mem_singleton]
  exact ⟨hp, trivial, fun y hy _ h => h ▸ hlt y (Array.mem_toList_iff.mp hy)⟩

/-! ## `ofList` -/

/-- One step of `ofList`'s fold: append `x` unless it is the last entry already. -/
private def dd (a : Array Nat) (x : Nat) : Array Nat :=
  if (a.back? == some x) = true then a else a.push x

private theorem ofList_eq (l : List Nat) :
    ofList l = (l.toArray.qsort (· < ·)).toList.foldl dd #[] := by
  rw [Array.foldl_toList]; rfl

private theorem mem_of_back? {a : Array Nat} {x : Nat} (h : a.back? = some x) : x ∈ a := by
  rw [Array.back?_eq_getElem?] at h
  exact Array.mem_of_getElem? h

private theorem mem_dd_fold : ∀ (L : List Nat) (acc : Array Nat) (x : Nat),
    x ∈ L.foldl dd acc ↔ x ∈ acc ∨ x ∈ L
  | [], acc, x => by simp
  | y :: L, acc, x => by
    rw [List.foldl_cons, mem_dd_fold L, List.mem_cons]
    unfold dd
    split
    · next h =>
      have hy : y ∈ acc := mem_of_back? (by simpa using h)
      constructor
      · rintro (h' | h')
        · exact .inl h'
        · exact .inr (.inr h')
      · rintro (h' | rfl | h')
        · exact .inl h'
        · exact .inl hy
        · exact .inr h'
    · rw [Array.mem_push]
      constructor
      · rintro ((h' | rfl) | h')
        · exact .inl h'
        · exact .inr (.inl rfl)
        · exact .inr (.inr h')
      · rintro (h' | rfl | h')
        · exact .inl (.inl h')
        · exact .inl (.inr rfl)
        · exact .inr h'

theorem mem_ofList {l : List Nat} {x : Nat} : x ∈ ofList l ↔ x ∈ l := by
  rw [ofList_eq, mem_dd_fold, Array.mem_toList_iff, (Array.qsort_perm l.toArray _ _ _).mem_iff]
  simp

/-- The largest member of a sorted set is its last entry. -/
private theorem back_of_max {acc : Array Nat} (h : SSet acc) {x : Nat} (hx : x ∈ acc)
    (hmax : ∀ y ∈ acc, y ≤ x) : acc.back? = some x := by
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
  rw [Array.back?_eq_getElem?]
  have hl : acc.size - 1 < acc.size := by omega
  by_cases hil : i = acc.size - 1
  · subst hil; exact Array.getElem?_eq_getElem hl
  · have := h.lt (Array.getElem?_eq_getElem hi) (Array.getElem?_eq_getElem hl) (by omega)
    have := hmax _ (Array.getElem_mem hl)
    omega

private theorem dd_sset : ∀ (L : List Nat) (acc : Array Nat), L.Pairwise (· ≤ ·) → SSet acc →
    (∀ y ∈ acc, ∀ z ∈ L, y ≤ z) → SSet (L.foldl dd acc)
  | [], _, _, h, _ => h
  | x :: L, acc, hL, h, hle => by
    rw [List.foldl_cons]
    obtain ⟨hx, hL⟩ := List.pairwise_cons.mp hL
    unfold dd
    split
    · exact dd_sset L acc hL h fun y hy z hz => hle y hy z (List.mem_cons_of_mem _ hz)
    · next hb =>
      refine dd_sset L _ hL (pairwise_push h fun y hy => ?_) fun y hy z hz => ?_
      · have hyx := hle y hy x List.mem_cons_self
        refine Nat.lt_of_le_of_ne hyx fun he => hb ?_
        subst he
        simp [back_of_max h hy fun w hw => hle w hw y List.mem_cons_self]
      · rcases Array.mem_push.mp hy with hy | rfl
        · exact hle y hy z (List.mem_cons_of_mem _ hz)
        · exact hx z hz

theorem ofList_sset (l : List Nat) : SSet (ofList l) := by
  rw [ofList_eq]
  exact dd_sset _ _ (Array.qsort_sorted_nat _) List.Pairwise.nil (fun _ h => by simp at h)

/-! ## `union` -/

/-- One step of the merge in `union`. -/
private def ustep (a b : Array Nat) (s : Array Nat × Nat × Nat) : Array Nat × Nat × Nat :=
  match a[s.2.1]?, b[s.2.2]? with
  | some x, some y =>
    if x < y then (s.1.push x, s.2.1 + 1, s.2.2)
    else if y < x then (s.1.push y, s.2.1, s.2.2 + 1)
    else (s.1.push x, s.2.1 + 1, s.2.2 + 1)
  | some x, none => (s.1.push x, s.2.1 + 1, s.2.2)
  | none, some y => (s.1.push y, s.2.1, s.2.2 + 1)
  | none, none => s

private theorem union_eq (a b : Array Nat) :
    union a b =
      ((List.range' 0 (a.size + b.size)).foldl (fun s _ => ustep a b s) (#[], 0, 0)).1 := by
  unfold union
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_one_sub_one, Nat.div_one, Array.mkEmpty_eq]
  rw [forIn_eq_foldl_of (fun s _ => ustep a b s)]
  · rfl
  · intro x s
    unfold ustep
    split <;> (try split) <;> (try split) <;> simp_all <;>
      (split <;> first | omega | rfl | (split <;> first | omega | rfl))

private theorem take_succ_of_getElem? {a : Array Nat} {i x : Nat} (h : a[i]? = some x) :
    a.toList.take (i + 1) = a.toList.take i ++ [x] := by
  rw [List.take_add_one, Array.getElem?_toList, h]; rfl

private theorem size_le_of_getElem?_none {a : Array Nat} {i : Nat} (h : a[i]? = none) :
    a.size ≤ i := by
  simpa using h

private theorem lt_size_of_getElem?_some {a : Array Nat} {i x : Nat} (h : a[i]? = some x) :
    i < a.size := by
  rcases Array.getElem?_eq_some_iff.mp h with ⟨hi, -⟩; exact hi

/-- Members and progress of the merge in `union`. -/
private def UMem (a b : Array Nat) (s : Array Nat × Nat × Nat) : Prop :=
  s.2.1 ≤ a.size ∧ s.2.2 ≤ b.size ∧ ∀ x, x ∈ s.1 ↔ x ∈ a.toList.take s.2.1 ∨ x ∈ b.toList.take s.2.2

private theorem ustep_mem {a b : Array Nat} {s : Array Nat × Nat × Nat} (h : UMem a b s) :
    UMem a b (ustep a b s) ∧
      min (s.2.1 + s.2.2 + 1) (a.size + b.size) ≤ (ustep a b s).2.1 + (ustep a b s).2.2 := by
  obtain ⟨out, i, j⟩ := s
  obtain ⟨hi, hj, hm⟩ := h
  simp only at hi hj hm ⊢
  unfold ustep
  simp only
  split
  · next x y ha hb =>
    have ha' := take_succ_of_getElem? ha
    have hb' := take_succ_of_getElem? hb
    have := lt_size_of_getElem?_some ha
    have := lt_size_of_getElem?_some hb
    split
    · refine ⟨⟨by dsimp only; omega, by dsimp only; omega, fun z => ?_⟩, by dsimp only; omega⟩
      simp only [Array.mem_push, hm, ha', List.mem_append, List.mem_singleton]; grind
    · split
      · refine ⟨⟨by dsimp only; omega, by dsimp only; omega, fun z => ?_⟩, by dsimp only; omega⟩
        simp only [Array.mem_push, hm, hb', List.mem_append, List.mem_singleton]; grind
      · refine ⟨⟨by dsimp only; omega, by dsimp only; omega, fun z => ?_⟩, by dsimp only; omega⟩
        simp only [Array.mem_push, hm, ha', hb', List.mem_append, List.mem_singleton]; grind
  · next x ha hb =>
    have ha' := take_succ_of_getElem? ha
    have := lt_size_of_getElem?_some ha
    refine ⟨⟨by dsimp only; omega, by dsimp only; omega, fun z => ?_⟩, by dsimp only; omega⟩
    simp only [Array.mem_push, hm, ha', List.mem_append, List.mem_singleton]; grind
  · next y ha hb =>
    have hb' := take_succ_of_getElem? hb
    have := lt_size_of_getElem?_some hb
    refine ⟨⟨by dsimp only; omega, by dsimp only; omega, fun z => ?_⟩, by dsimp only; omega⟩
    simp only [Array.mem_push, hm, hb', List.mem_append, List.mem_singleton]; grind
  · next ha hb =>
    have := size_le_of_getElem?_none ha
    have := size_le_of_getElem?_none hb
    exact ⟨⟨hi, hj, hm⟩, by dsimp only; omega⟩

private theorem ufold_mem {a b : Array Nat} :
    ∀ (L : List Nat) (s : Array Nat × Nat × Nat), UMem a b s →
      UMem a b (L.foldl (fun s _ => ustep a b s) s) ∧
        min (L.length + s.2.1 + s.2.2) (a.size + b.size) ≤
          (L.foldl (fun s _ => ustep a b s) s).2.1 + (L.foldl (fun s _ => ustep a b s) s).2.2
  | [], s, h => ⟨h, by simp only [List.length_nil, List.foldl_nil]; omega⟩
  | _ :: L, s, h => by
    obtain ⟨h', hp⟩ := ustep_mem h
    obtain ⟨r, hr⟩ := ufold_mem L _ h'
    refine ⟨r, ?_⟩
    simp only [List.length_cons, List.foldl_cons]
    have := h.1; have := h.2.1; have := h'.1; have := h'.2.1
    omega

theorem mem_union {a b : Array Nat} {x : Nat} : x ∈ union a b ↔ x ∈ a ∨ x ∈ b := by
  rw [union_eq]
  obtain ⟨⟨hi, hj, hm⟩, hp⟩ := ufold_mem (a := a) (b := b) (List.range' 0 (a.size + b.size))
    (#[], 0, 0) ⟨Nat.zero_le _, Nat.zero_le _, fun x => by simp⟩
  simp only [List.length_range', Nat.add_zero] at hp
  generalize List.foldl (fun s _ => ustep a b s) (#[], 0, 0) (List.range' 0 (a.size + b.size)) = r
    at hi hj hm hp
  rw [hm, show r.2.1 = a.size by omega, show r.2.2 = b.size by omega]
  simp only [← Array.length_toList, List.take_length, Array.mem_toList_iff]

/-- The merge in `union` is sorted and below what remains of `a` and `b`. -/
private def USorted (a b : Array Nat) (s : Array Nat × Nat × Nat) : Prop :=
  s.1.toList.Pairwise (· < ·) ∧
    (∀ y ∈ s.1, ∀ i z, s.2.1 ≤ i → a[i]? = some z → y < z) ∧
    (∀ y ∈ s.1, ∀ j z, s.2.2 ≤ j → b[j]? = some z → y < z)

private theorem ustep_sorted {a b : Array Nat} (ha : SSet a) (hb : SSet b)
    {s : Array Nat × Nat × Nat}
    (h : USorted a b s) : USorted a b (ustep a b s) := by
  obtain ⟨out, i, j⟩ := s
  obtain ⟨hp, hai, hbj⟩ := h
  simp only at hp hai hbj
  unfold ustep
  simp only
  split
  · next x y hx hy =>
    split
    · next hxy =>
      refine ⟨pairwise_push hp fun z hz => hai z hz i x (Nat.le_refl _) hx, ?_, ?_⟩
      · dsimp only; intro z hz i' w hi' hw
        rcases Array.mem_push.mp hz with hz | rfl
        · exact hai z hz i' w (by omega) hw
        · exact ha.lt hx hw (by omega)
      · dsimp only; intro z hz j' w hj' hw
        rcases Array.mem_push.mp hz with hz | rfl
        · exact hbj z hz j' w hj' hw
        · exact Nat.lt_of_lt_of_le hxy (hb.le hy hw hj')
    · next hxy =>
      split
      · next hyx =>
        refine ⟨pairwise_push hp fun z hz => hbj z hz j y (Nat.le_refl _) hy, ?_, ?_⟩
        · dsimp only; intro z hz i' w hi' hw
          rcases Array.mem_push.mp hz with hz | rfl
          · exact hai z hz i' w hi' hw
          · exact Nat.lt_of_lt_of_le hyx (ha.le hx hw hi')
        · dsimp only; intro z hz j' w hj' hw
          rcases Array.mem_push.mp hz with hz | rfl
          · exact hbj z hz j' w (by omega) hw
          · exact hb.lt hy hw (by omega)
      · next hyx =>
        have hxy' : x = y := by omega
        subst hxy'
        refine ⟨pairwise_push hp fun z hz => hai z hz i x (Nat.le_refl _) hx, ?_, ?_⟩
        · dsimp only; intro z hz i' w hi' hw
          rcases Array.mem_push.mp hz with hz | rfl
          · exact hai z hz i' w (by omega) hw
          · exact ha.lt hx hw (by omega)
        · dsimp only; intro z hz j' w hj' hw
          rcases Array.mem_push.mp hz with hz | rfl
          · exact hbj z hz j' w (by omega) hw
          · exact hb.lt hy hw (by omega)
  · next x hx hy =>
    have hbs := size_le_of_getElem?_none hy
    refine ⟨pairwise_push hp fun z hz => hai z hz i x (Nat.le_refl _) hx, ?_, ?_⟩
    · dsimp only; intro z hz i' w hi' hw
      rcases Array.mem_push.mp hz with hz | rfl
      · exact hai z hz i' w (by omega) hw
      · exact ha.lt hx hw (by omega)
    · dsimp only; intro z hz j' w hj' hw
      have := lt_size_of_getElem?_some hw
      omega
  · next y hx hy =>
    have has := size_le_of_getElem?_none hx
    refine ⟨pairwise_push hp fun z hz => hbj z hz j y (Nat.le_refl _) hy, ?_, ?_⟩
    · dsimp only; intro z hz i' w hi' hw
      have := lt_size_of_getElem?_some hw
      omega
    · dsimp only; intro z hz j' w hj' hw
      rcases Array.mem_push.mp hz with hz | rfl
      · exact hbj z hz j' w (by omega) hw
      · exact hb.lt hy hw (by omega)
  · exact ⟨hp, hai, hbj⟩

theorem union_sset {a b : Array Nat} (ha : SSet a) (hb : SSet b) : SSet (union a b) := by
  rw [union_eq]
  suffices ∀ (L : List Nat) (s : Array Nat × Nat × Nat), USorted a b s →
      USorted a b (L.foldl (fun s _ => ustep a b s) s) from
    (this _ _ ⟨List.Pairwise.nil, fun _ h => by simp at h, fun _ h => by simp at h⟩).1
  intro L
  induction L with
  | nil => exact fun _ h => h
  | cons _ L ih => exact fun s h => ih _ (ustep_sorted ha hb h)

/-! ## `diff` -/

/-- The inner `while` loop of `diff`: skip the entries of `b` below `x`. -/
private def wloop (b : Array Nat) (x j : Nat) : Nat :=
  (forIn Lean.Loop.mk j fun _ j =>
    if (decide (j < b.size) && decide (b[j]! < x)) = true then pure (ForInStep.yield (j + 1))
    else pure (ForInStep.done j) : Id Nat).run

private theorem getElem!_eq {b : Array Nat} {j : Nat} (h : j < b.size) : b[j]! = b[j] := by
  simp [getElem!_pos, h]

private theorem wloop_eq (b : Array Nat) (x j : Nat) :
    wloop b x j = if j < b.size ∧ b[j]! < x then wloop b x (j + 1) else j := by
  unfold wloop
  simp only [ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  by_cases h : j < b.size ∧ b[j]! < x
  · have h₂ : b[j] < x := getElem!_eq h.1 ▸ h.2
    simp [h, h₂]
  · simp only [h, ↓reduceIte]
    have : (decide (j < b.size) && decide (b[j]! < x)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp [this]

private theorem wloop_spec (b : Array Nat) (x : Nat) :
    ∀ n j, b.size - j = n →
      j ≤ wloop b x j ∧ (∀ t (h : t < b.size), j ≤ t → t < wloop b x j → b[t] < x) ∧
        (wloop b x j < b.size → ¬ b[wloop b x j]! < x) := by
  intro n
  induction n with
  | zero =>
    intro j hj
    rw [wloop_eq]
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    exact ⟨Nat.le_refl _, fun _ _ _ _ => by omega, fun _ => by omega⟩
  | succ n ih =>
    intro j hj
    rw [wloop_eq]
    split
    · next h =>
      obtain ⟨h₁, h₂, h₃⟩ := ih (j + 1) (by omega)
      refine ⟨by omega, fun t ht hjt htw => ?_, h₃⟩
      by_cases htj : t = j
      · subst htj; rw [← getElem!_eq ht]; exact h.2
      · exact h₂ t ht (by omega) htw
    · next h =>
      exact ⟨Nat.le_refl _, fun _ _ _ _ => by omega, fun hj => by omega⟩

/-- One element of `a` in `diff a b`. -/
private def dstep (b : Array Nat) (s : Array Nat × Nat) (x : Nat) : Array Nat × Nat :=
  if (!(decide (wloop b x s.2 < b.size) && b[wloop b x s.2]! == x)) = true then
    (s.1.push x, wloop b x s.2)
  else (s.1, wloop b x s.2)

private theorem forIn_toList_eq {α β : Type} (xs : Array α) (init : β)
    (f : α → β → Id (ForInStep β)) :
    forIn xs init f = forIn xs.toList init f := (Array.forIn_toList).symm

private theorem diff_eq (a b : Array Nat) : diff a b = (a.toList.foldl (dstep b) (#[], 0)).1 := by
  unfold diff
  simp only [Array.mkEmpty_eq]
  rw [forIn_toList_eq, forIn_eq_foldl_of (dstep b)]
  · rfl
  · intro x s
    unfold dstep wloop
    rw [show ∀ (m : Id Nat) (g : Nat → Id (ForInStep (Array Nat × Nat))), m >>= g = g m.run
      from fun _ _ => rfl]
    rw [apply_ite (fun s => (pure (ForInStep.yield s) : Id _))]

private theorem dstep_sub (b : Array Nat) (s : Array Nat × Nat) (x : Nat) :
    (dstep b s x).1.toList.Sublist (s.1.toList ++ [x]) := by
  unfold dstep
  split
  · simp
  · exact List.sublist_append_left _ _

private theorem dfold_sub (b : Array Nat) :
    ∀ (L : List Nat) (s : Array Nat × Nat), (L.foldl (dstep b) s).1.toList.Sublist (s.1.toList ++ L)
  | [], s => by simp
  | x :: L, s => by
    rw [List.foldl_cons]
    refine (dfold_sub b L _).trans ?_
    have := (dstep_sub b s x).append_right L
    simpa using this

private theorem diff_sublist (a b : Array Nat) : (diff a b).toList.Sublist a.toList := by
  rw [diff_eq]
  simpa using dfold_sub b a.toList (#[], 0)

theorem diff_sset {a b : Array Nat} (ha : SSet a) : SSet (diff a b) :=
  ha.sublist (diff_sublist a b)

private theorem mem_dstep_of_not_mem {b : Array Nat} {x : Nat} (hx : x ∉ b) (s : Array Nat × Nat) :
    x ∈ (dstep b s x).1 := by
  unfold dstep
  split
  · exact Array.mem_push_self
  · next hc =>
    simp at hc
    rw [getElem!_eq hc.1] at hc
    exact absurd (hc.2 ▸ Array.getElem_mem hc.1) hx

private theorem mem_dstep_of_mem {b : Array Nat} {x y : Nat} {s : Array Nat × Nat} (hy : y ∈ s.1) :
    y ∈ (dstep b s x).1 := by
  unfold dstep
  split
  · exact Array.mem_push_of_mem _ hy
  · exact hy

private theorem mem_dfold (b : Array Nat) {y : Nat} :
    ∀ (L : List Nat) (s : Array Nat × Nat), (y ∈ s.1 ∨ (y ∈ L ∧ y ∉ b)) →
      y ∈ (L.foldl (dstep b) s).1
  | [], s, h => by simpa using h
  | x :: L, s, h => by
    rw [List.foldl_cons]
    refine mem_dfold b L _ ?_
    rcases h with h | ⟨h, hb⟩
    · exact .inl (mem_dstep_of_mem h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inl (mem_dstep_of_not_mem hb s)
      · exact .inr ⟨h, hb⟩

theorem mem_diff_of_mem {a b : Array Nat} {x : Nat} (ha : x ∈ a) (hb : x ∉ b) :
    x ∈ diff a b := by
  rw [diff_eq]
  exact mem_dfold b a.toList _ (.inr ⟨Array.mem_toList_iff.mpr ha, hb⟩)

/-- What `diff` keeps from `a` is not in the sorted `b`. -/
private theorem dfold_not_mem {b : Array Nat} (hb : SSet b) :
    ∀ (L : List Nat) (s : Array Nat × Nat), L.Pairwise (· < ·) →
      (∀ t (h : t < b.size), t < s.2 → ∀ z ∈ L, b[t] < z) → (∀ y ∈ s.1, y ∉ b) →
      ∀ y ∈ (L.foldl (dstep b) s).1, y ∉ b
  | [], _, _, _, hs => by simpa using hs
  | x :: L, s, hL, hj, hs => by
    rw [List.foldl_cons]
    obtain ⟨hx, hL⟩ := List.pairwise_cons.mp hL
    obtain ⟨hw₁, hw₂, hw₃⟩ := wloop_spec b x _ s.2 rfl
    -- every entry of `b` before the new pointer is below `x`
    have below : ∀ t (h : t < b.size), t < wloop b x s.2 → b[t] < x := fun t h ht => by
      by_cases hts : t < s.2
      · exact hj t h hts x List.mem_cons_self
      · exact hw₂ t h (by omega) ht
    refine dfold_not_mem hb L _ hL ?_ ?_
    · intro t h ht z hz
      exact Nat.lt_trans (below t h (by unfold dstep at ht; split at ht <;> exact ht)) (hx z hz)
    · intro y hy
      unfold dstep at hy
      split at hy
      · next hc =>
        rcases Array.mem_push.mp hy with hy | hyx
        · exact hs y hy
        · rw [hyx]
          intro hyb
          obtain ⟨t, ht, he⟩ := Array.getElem_of_mem hyb
          by_cases htw : t < wloop b x s.2
          · exact Nat.lt_irrefl _ (he ▸ below t ht htw)
          · have hws : wloop b x s.2 < b.size := by omega
            have h₁ := hw₃ hws
            rw [getElem!_eq hws] at h₁
            simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
              Nat.not_lt, beq_eq_false_iff_ne, ne_eq] at hc
            rcases hc with hc | hc
            · omega
            · rw [getElem!_eq hws] at hc
              have := hb.le (Array.getElem?_eq_getElem hws) (Array.getElem?_eq_getElem ht)
                (by omega)
              omega
      · exact hs y hy

theorem mem_diff {a b : Array Nat} (ha : SSet a) (hb : SSet b) {x : Nat} :
    x ∈ diff a b ↔ x ∈ a ∧ x ∉ b := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => mem_diff_of_mem h.1 h.2⟩
  · exact Array.mem_toList_iff.mp ((diff_sublist a b).subset (Array.mem_toList_iff.mpr h))
  · rw [diff_eq] at h
    exact dfold_not_mem hb a.toList _ ha (fun _ _ h => by simp at h) (fun _ h => by simp at h) x h

/-! ## `genKill` -/

/-- One use in `genKill`: gathered unless defined earlier in the block. -/
private def gstep (kill : Std.HashSet Nat) (gen : List Nat) (u : Nat) : List Nat :=
  if (!kill.contains u) = true then u :: gen else gen

private theorem gloop_eq (kill : Std.HashSet Nat) (us gen : List Nat) :
    forIn (m := Id) us gen (fun u gen =>
      if (!kill.contains u) = true then pure (ForInStep.yield (u :: gen))
      else pure (ForInStep.yield gen)) = pure (us.foldl (gstep kill) gen) :=
  forIn_eq_foldl_of _ fun u g => by unfold gstep; split <;> rfl

private def istep (s : List Nat × Std.HashSet Nat) (i : Instr Nat) : List Nat × Std.HashSet Nat :=
  ((instrUses i).foldl (gstep s.2) s.1, (instrDefs i).foldl (fun k d => k.insert d) s.2)

/-- One instruction in `genKill`. -/
private theorem genKill_eq (b : Block Nat) :
    genKill b = (ofList ((termUses b.term).foldl (gstep (b.instrs.foldl istep ([], ∅)).2)
      (b.instrs.foldl istep ([], ∅)).1), ofList (b.instrs.foldl istep ([], ∅)).2.toList) := by
  unfold genKill
  simp only [gloop_eq, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

private theorem mem_gfold_of_mem {kill : Std.HashSet Nat} :
    ∀ (us gen : List Nat) {x : Nat}, x ∈ gen → x ∈ us.foldl (gstep kill) gen
  | [], _, _, h => h
  | _ :: us, _, _, h => mem_gfold_of_mem us _ (by
      unfold gstep
      split
      · exact List.mem_cons_of_mem _ h
      · exact h)

private theorem mem_gfold {kill : Std.HashSet Nat} :
    ∀ (us gen : List Nat) {x : Nat}, x ∈ us → x ∉ kill → x ∈ us.foldl (gstep kill) gen
  | [], _, _, h, _ => by simp at h
  | u :: us, gen, x, h, hk => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · apply mem_gfold_of_mem
      unfold gstep
      split
      · exact List.mem_cons_self
      · next hc => exact absurd (by simpa using hc) hk
    · exact mem_gfold us _ h hk

private theorem mem_kfold : ∀ (ds : List Nat) (k : Std.HashSet Nat) {x : Nat},
    x ∈ ds.foldl (fun k d => k.insert d) k ↔ x ∈ k ∨ x ∈ ds
  | [], k, x => by simp
  | d :: ds, k, x => by
    rw [List.foldl_cons, mem_kfold ds, Std.HashSet.mem_insert, List.mem_cons, beq_iff_eq]
    constructor
    · rintro ((rfl | h) | h)
      · exact .inr (.inl rfl)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | rfl | h)
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
      · exact .inr h

private theorem ifold_gen : ∀ (is : List (Instr Nat)) (s : List Nat × Std.HashSet Nat) {x : Nat},
    x ∈ s.1 → x ∈ (is.foldl istep s).1
  | [], _, _, h => h
  | _ :: is, _, _, h => ifold_gen is _ (mem_gfold_of_mem _ _ h)

/-- The registers live before a suffix of a block are gathered in `gen` or untouched by
the whole block. -/
private theorem ifold_live (t : Term Nat) (out : List Nat) :
    ∀ (is : List (Instr Nat)) (s : List Nat × Std.HashSet Nat) {x : Nat}, x ∉ s.2 →
      x ∈ liveFrom (termUses t ++ out) is →
      x ∈ (termUses t).foldl (gstep (is.foldl istep s).2) (is.foldl istep s).1 ∨
        (x ∈ out ∧ x ∉ (is.foldl istep s).2)
  | [], s, x, hk, h => by
    simp only [liveFrom, List.mem_append] at h
    rcases h with h | h
    · exact .inl (mem_gfold _ _ h hk)
    · exact .inr ⟨h, hk⟩
  | i :: is, s, x, hk, h => by
    simp only [List.foldl_cons]
    rcases mem_liveStep.mp h with hu | ⟨h', hd, -⟩
    · exact .inl (mem_gfold_of_mem _ _ (ifold_gen is _ (mem_gfold _ _ hu hk)))
    · exact ifold_live t out is _ (fun hx => ((mem_kfold _ _).mp hx).elim hk hd) h'

theorem genKill_sset (b : Block Nat) : SSet (genKill b).1 ∧ SSet (genKill b).2 := by
  rw [genKill_eq]
  exact ⟨ofList_sset _, ofList_sset _⟩

/-- The registers live before the instructions of a block, given its terminator's uses and
`out`, are upward-exposed uses (`gen`) or registers of `out` the block does not define. -/
theorem liveFrom_genKill (b : Block Nat) (out : List Nat) {x : Nat}
    (h : x ∈ liveFrom (termUses b.term ++ out) b.instrs) :
    x ∈ (genKill b).1 ∨ (x ∈ out ∧ x ∉ (genKill b).2) := by
  rw [genKill_eq]
  simp only [mem_ofList, Std.HashSet.mem_toList]
  exact ifold_live b.term out b.instrs ([], ∅) (Std.HashSet.not_mem_empty) h

end Silmaril.Compile.Target.RegAlloc
