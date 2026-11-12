module

public import Silmaril.Compiler.Target.RenameCheck.Defs
public import Silmaril.Compiler.Target.QSortPerm.Defs
public import Std.Data.HashMap.Lemmas
public import Std.Data.TreeMap.Lemmas
import Std.Data.DTreeMap.Internal.WF.Lemmas

/-! # `assign` separates registers whose intervals meet

Every register of `m` gets a number from `assign k m`: a colour `c < k` whose tree of
disjoint intervals its interval does not meet (`meets` asks the tree for the interval
starting last at or before its end), or a fresh number `≥ k` of its own. So two
registers whose intervals share a position get different numbers (`assign_sep`).
-/

@[expose] public section

namespace Silmaril.Compile.Target.RegAlloc

open Silmaril.Machine Silmaril.Machine.Lir

/-- The interval of `v` in `m` contains position `q`. -/
def Covers (m : Std.HashMap Nat Info) (v q : Nat) : Prop :=
  ∃ i, m[v]? = some i ∧ i.start ≤ q ∧ q ≤ i.stop

/-! ## `meets` -/

open Std.DTreeMap.Internal in
/-- `getEntryLE?` is the last entry of the sorted entry list whose key is at most `e`. -/
private theorem getEntryLE?_eq_findRev? (t : Std.TreeMap Nat Nat) (e : Nat) :
    t.getEntryLE? e = t.toList.findRev? (fun p => (compare p.1 e).isLE) := by
  show Impl.Const.getEntryLE? e t.inner.inner = (Impl.Const.toList t.inner.inner).findRev? _
  rw [Impl.Const.getEntryLE?_eq_map, Impl.getEntryLE?_eq_findRev? t.inner.wf.ordered,
    Impl.Const.toList_eq_toListModel_map]
  simp [List.findRev?_eq_find?_reverse, ← List.map_reverse, List.find?_map]

/-- A tree of colour intervals (start ↦ stop): nonempty and pairwise disjoint. -/
private def TreeOk (t : Std.TreeMap Nat Nat) : Prop :=
  (∀ a b : Nat, t[a]? = some b → a ≤ b) ∧
    ∀ a b c d : Nat, t[a]? = some b → t[c]? = some d → a < c → b < c

/-- If `[s, e]` does not meet the tree, it meets none of its intervals. -/
private theorem not_meet_of_meets {t : Std.TreeMap Nat Nat} (ht : TreeOk t) {s e : Nat}
    (h : meets t s e = false) {a b : Nat} (hab : t[a]? = some b) : ¬ (a ≤ e ∧ s ≤ b) := by
  rintro ⟨hae, hsb⟩
  have hmem : (a, b) ∈ t.toList := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hab
  unfold meets at h
  rw [getEntryLE?_eq_findRev?, List.findRev?_eq_find?_reverse] at h
  cases hg : t.toList.reverse.find? (fun p => (compare p.1 e).isLE) with
  | none =>
    rw [List.find?_eq_none] at hg
    have := hg (a, b) (List.mem_reverse.mpr hmem)
    simp [Nat.isLE_compare, hae] at this
  | some x =>
    obtain ⟨s₀, e₀⟩ := x
    rw [hg] at h
    simp only [decide_eq_false_iff_not, Nat.not_le] at h
    obtain ⟨hp, as, bs, hrev, has⟩ := List.find?_eq_some_iff_append.mp hg
    have hx : t[s₀]? = some e₀ := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp
      (List.mem_reverse.mp (hrev ▸ List.mem_append_right _ List.mem_cons_self))
    have hlist : t.toList = bs.reverse ++ (s₀, e₀) :: as.reverse := by
      rw [← List.reverse_reverse t.toList, hrev]; simp
    have hsorted := Std.TreeMap.ordered_keys_toList (t := t)
    rw [hlist] at hmem hsorted
    rcases List.mem_append.mp hmem with hb | hb
    · have hlt := (List.pairwise_append.mp hsorted).2.2 _ hb _ List.mem_cons_self
      simp only [Nat.compare_eq_lt] at hlt
      have := ht.2 a b s₀ e₀ hab hx hlt
      have := ht.1 s₀ e₀ hx
      omega
    · rcases List.mem_cons.mp hb with hb | hb
      · simp only [Prod.mk.injEq] at hb
        omega
      · have h₃ : (compare a e).isLE = false := by simpa using has _ (List.mem_reverse.mp hb)
        rw [Nat.isLE_compare.mpr hae] at h₃
        cases h₃

/-- Inserting an interval that meets none of the tree's keeps the tree disjoint, and
overwrites nothing. -/
private theorem treeOk_insert {t : Std.TreeMap Nat Nat} (ht : TreeOk t) {s e : Nat} (hse : s ≤ e)
    (h : meets t s e = false) : t[s]? = none ∧ TreeOk (t.insert s e) := by
  have nm : ∀ {a b : Nat}, t[a]? = some b → ¬ (a ≤ e ∧ s ≤ b) := fun hab =>
    not_meet_of_meets ht h hab
  have hs : t[s]? = none := by
    cases hts : t[s]? with
    | none => rfl
    | some d => exact absurd ⟨hse, ht.1 s d hts⟩ (nm hts)
  refine ⟨hs, ?_, ?_⟩
  · intro a b hab
    rw [Std.TreeMap.getElem?_insert] at hab
    split at hab
    · next hc => cases hab; rw [Nat.compare_eq_eq] at hc; omega
    · exact ht.1 a b hab
  · intro a b c d hab hcd hac
    rw [Std.TreeMap.getElem?_insert] at hab hcd
    split at hab <;> split at hcd
    · next h₁ h₂ => rw [Nat.compare_eq_eq] at h₁ h₂; omega
    · next h₁ _ =>
      cases hab; rw [Nat.compare_eq_eq] at h₁; subst h₁
      have := nm hcd
      have := ht.1 c d hcd
      omega
    · next h₂ =>
      cases hcd; rw [Nat.compare_eq_eq] at h₂; subst h₂
      have := nm hab
      have := ht.1 a b hab
      omega
    · exact ht.2 a b c d hab hcd hac

/-! ## The loop of `assign` -/

/-- One step of the loop of `assign`. -/
private def assignStep (k : Nat) (s : Array (Std.TreeMap Nat Nat) × Std.HashMap Nat Nat × Nat)
    (x : Nat × Info) : Array (Std.TreeMap Nat Nat) × Std.HashMap Nat Nat × Nat :=
  match List.find? (fun c => !meets s.1[c]! x.2.start x.2.stop) (List.range k) with
  | some c => (s.1.modify c fun t => t.insert x.2.start x.2.stop, s.2.1.insert x.1 c, s.2.2)
  | none => (s.1, s.2.1.insert x.1 s.2.2, s.2.2 + 1)

private theorem assign_eq (k : Nat) (m : Std.HashMap Nat Info) :
    ∃ order : Array (Nat × Info), order.toList.Perm m.toList ∧
      assign k m = (order.toList.foldl (assignStep k) (Array.replicate k ∅, ∅, k)).2.1 := by
  refine ⟨m.toArray.qsort fun (v, a) (w, b) =>
    a.weight > b.weight || (a.weight == b.weight &&
      (a.start < b.start || (a.start == b.start && v < w))), ?_, ?_⟩
  · refine (Array.perm_iff_toList_perm.mp (Array.qsort_perm _ _ _ _)).trans ?_
    simp [← Std.HashMap.toArray_toList]
  unfold assign
  simp only [Id.run]
  generalize (m.toArray.qsort _) = xs
  generalize ((Array.replicate k (∅ : Std.TreeMap Nat Nat), (∅ : Std.HashMap Nat Nat), k) :
    Array (Std.TreeMap Nat Nat) × Std.HashMap Nat Nat × Nat) = s
  rcases xs with ⟨l⟩
  induction l generalizing s with
  | nil => rfl
  | cons x l ih =>
    simp only [List.forIn_toArray, List.forIn_cons] at ih ⊢
    rw [List.foldl_cons, assignStep]
    split <;> next h => simp only [h, pure_bind]; exact ih _

/-- Two intervals share a position. -/
private def Meet (i j : Info) : Prop := i.start ≤ j.stop ∧ j.start ≤ i.stop

/-- The invariant of the loop of `assign` after the entries `pre`. -/
private structure AssignInv (k : Nat) (pre : List (Nat × Info))
    (s : Array (Std.TreeMap Nat Nat) × Std.HashMap Nat Nat × Nat) : Prop where
  size : s.1.size = k
  le : k ≤ s.2.2
  tree : ∀ c < k, TreeOk s.1[c]!
  num : ∀ x ∈ pre, ∃ n, s.2.1[x.1]? = some n ∧
    ((n < k ∧ (s.1[n]!)[x.2.start]? = some x.2.stop) ∨ (k ≤ n ∧ n < s.2.2))
  sep : ∀ x ∈ pre, ∀ y ∈ pre, x.1 ≠ y.1 → Meet x.2 y.2 → s.2.1[x.1]? ≠ s.2.1[y.1]?

private theorem getElem!_modify_tree {xs : Array (Std.TreeMap Nat Nat)} {c d : Nat}
    {f : Std.TreeMap Nat Nat → Std.TreeMap Nat Nat} (hc : c < xs.size) :
    (xs.modify c f)[d]! = if c = d then f xs[c]! else xs[d]! := by
  simp only [getElem!_def, Array.getElem?_modify]
  by_cases h : c = d
  · subst h; simp [getElem?_pos xs c hc]
  · simp [h]

private theorem assignInv_step {k : Nat} {pre : List (Nat × Info)} {s} (h : AssignInv k pre s)
    {x : Nat × Info} (hx : ∀ y ∈ pre, x.1 ≠ y.1) (hwf : x.2.start ≤ x.2.stop) :
    AssignInv k (pre ++ [x]) (assignStep k s x) := by
  obtain ⟨hsize, hle, htree, hnum, hsep⟩ := h
  have hold : ∀ y ∈ pre, ∀ n, (s.2.1.insert x.1 n)[y.1]? = s.2.1[y.1]? := by
    intro y hy n
    rw [Std.HashMap.getElem?_insert]
    simp [hx y hy]
  have hnew : ∀ n, (s.2.1.insert x.1 n)[x.1]? = some n := by
    intro n; simp
  unfold assignStep
  split
  · next c hc =>
    have hc' := List.find?_some hc
    have hck : c < k := List.mem_range.mp (List.mem_of_find?_eq_some hc)
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hc'
    obtain ⟨hnone, htc⟩ := treeOk_insert (htree c hck) hwf hc'
    have hmod : ∀ d, (s.1.modify c fun t => t.insert x.2.start x.2.stop)[d]! =
        if c = d then s.1[c]!.insert x.2.start x.2.stop else s.1[d]! :=
      fun d => getElem!_modify_tree (by omega)
    refine ⟨by simpa using hsize, hle, ?_, ?_, ?_⟩
    · intro d hd
      rw [hmod]
      split
      · next h => subst h; exact htc
      · exact htree d hd
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨n, hn, hn'⟩ := hnum y hy
        refine ⟨n, by rw [hold y hy]; exact hn, ?_⟩
        rcases hn' with ⟨hnk, hnt⟩ | hn'
        · refine .inl ⟨hnk, ?_⟩
          rw [hmod]
          split
          · next h =>
            subst h
            rw [Std.TreeMap.getElem?_insert]
            split
            · next he => rw [Nat.compare_eq_eq] at he; rw [← he, hnone] at hnt; cases hnt
            · exact hnt
          · exact hnt
        · exact .inr hn'
      · simp only [List.mem_singleton] at hy
        subst hy
        refine ⟨c, hnew c, .inl ⟨hck, ?_⟩⟩
        rw [hmod]
        simp
    · -- a new register is separated from every earlier one
      have key : ∀ y ∈ pre, Meet x.2 y.2 → s.2.1[y.1]? ≠ some c := by
        intro y hy hm hyc
        obtain ⟨n, hn, hn'⟩ := hnum y hy
        rw [hn, Option.some.injEq] at hyc
        subst hyc
        rcases hn' with ⟨-, hnt⟩ | ⟨hkn, -⟩
        · exact not_meet_of_meets (htree _ hck) hc' hnt ⟨hm.2, hm.1⟩
        · omega
      intro y hy z hz hyz hm
      rcases List.mem_append.mp hy with hy | hy <;> rcases List.mem_append.mp hz with hz | hz
      · rw [hold y hy, hold z hz]; exact hsep y hy z hz hyz hm
      · rw [List.mem_singleton] at hz; rw [hz] at hm ⊢
        rw [hold y hy, hnew]; exact key y hy ⟨hm.2, hm.1⟩
      · rw [List.mem_singleton] at hy; rw [hy] at hm ⊢
        rw [hold z hz, hnew]; exact (key z hz hm).symm
      · rw [List.mem_singleton] at hy hz; rw [hy, hz] at hyz; exact absurd rfl hyz
  · next hc =>
    refine ⟨hsize, by simp only; omega, htree, ?_, ?_⟩
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨n, hn, hn'⟩ := hnum y hy
        refine ⟨n, by simp only; rw [hold y hy]; exact hn, ?_⟩
        rcases hn' with hn' | hn'
        · exact .inl hn'
        · exact .inr ⟨hn'.1, by simp only; omega⟩
      · simp only [List.mem_singleton] at hy
        subst hy
        exact ⟨s.2.2, hnew _, .inr ⟨hle, by simp only; omega⟩⟩
    · have key : ∀ y ∈ pre, s.2.1[y.1]? ≠ some s.2.2 := by
        intro y hy hyn
        obtain ⟨n, hn, hn'⟩ := hnum y hy
        rw [hn, Option.some.injEq] at hyn
        subst hyn
        rcases hn' with ⟨hnk, -⟩ | ⟨-, hn⟩ <;> omega
      intro y hy z hz hyz hm
      simp only
      rcases List.mem_append.mp hy with hy | hy <;> rcases List.mem_append.mp hz with hz | hz
      · rw [hold y hy, hold z hz]; exact hsep y hy z hz hyz hm
      · rw [List.mem_singleton] at hz; rw [hz] at hm ⊢
        rw [hold y hy, hnew]; exact key y hy
      · rw [List.mem_singleton] at hy; rw [hy] at hm ⊢
        rw [hold z hz, hnew]; exact (key z hz).symm
      · rw [List.mem_singleton] at hy hz; rw [hy, hz] at hyz; exact absurd rfl hyz

private theorem assignInv_foldl {k : Nat} :
    ∀ (l pre : List (Nat × Info)) s, AssignInv k pre s →
      l.Pairwise (fun x y => x.1 ≠ y.1) → (∀ x ∈ l, ∀ y ∈ pre, x.1 ≠ y.1) →
      (∀ x ∈ l, x.2.start ≤ x.2.stop) → AssignInv k (pre ++ l) (l.foldl (assignStep k) s)
  | [], pre, s, h, _, _, _ => by simpa using h
  | x :: l, pre, s, h, hp, hd, hwf => by
    rw [List.foldl_cons, show pre ++ x :: l = (pre ++ [x]) ++ l by simp]
    obtain ⟨hx, hp⟩ := List.pairwise_cons.mp hp
    refine assignInv_foldl l _ _ (assignInv_step h (hd x List.mem_cons_self)
      (hwf x List.mem_cons_self)) hp ?_ (fun y hy => hwf y (List.mem_cons_of_mem _ hy))
    intro y hy z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hd y (List.mem_cons_of_mem _ hy) z hz
    · simp only [List.mem_singleton] at hz; subst hz; exact fun h => hx y hy h.symm

theorem assign_sep (k : Nat) (m : Std.HashMap Nat Info)
    (hwf : ∀ (v : Nat) (i : Info), m[v]? = some i → i.start ≤ i.stop)
    {u w q : Nat} (huw : u ≠ w) (hu : Covers m u q) (hw : Covers m w q) :
    (assign k m).getD u u ≠ (assign k m).getD w w := by
  obtain ⟨order, hperm, heq⟩ := assign_eq k m
  have init : AssignInv k [] (Array.replicate k ∅, ∅, k) :=
    ⟨by simp, le_refl _, fun c hc => by
      simp only [getElem!_def, Array.getElem?_replicate, hc]
      exact ⟨by simp, by simp⟩, by simp, by simp⟩
  have hdist : order.toList.Pairwise (fun x y => x.1 ≠ y.1) :=
    (hperm.pairwise_iff (fun h => Ne.symm h)).mpr
      (Std.HashMap.distinct_keys_toList.imp fun h => by simpa using h)
  have inv := assignInv_foldl order.toList [] _ init hdist (by simp) fun x hx =>
    hwf x.1 x.2 (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (hperm.subset hx))
  rw [List.nil_append] at inv
  obtain ⟨iu, hiu, hu₁, hu₂⟩ := hu
  obtain ⟨iw, hiw, hw₁, hw₂⟩ := hw
  have mu : (u, iu) ∈ order.toList :=
    hperm.symm.subset (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hiu)
  have mw : (w, iw) ∈ order.toList :=
    hperm.symm.subset (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hiw)
  have hne := inv.sep _ mu _ mw huw (show Meet iu iw from ⟨by omega, by omega⟩)
  obtain ⟨nu, hnu, -⟩ := inv.num _ mu
  obtain ⟨nw, hnw, -⟩ := inv.num _ mw
  simp only at hne hnu hnw
  rw [heq, Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getD_eq_getD_getElem?, hnu, hnw]
  rw [hnu, hnw] at hne
  simpa using hne

end Silmaril.Compile.Target.RegAlloc
