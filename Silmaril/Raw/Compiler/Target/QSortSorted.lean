module

public import Init.Data.Array.Perm
public import Init.Data.Vector.Lemmas
import all Init.Data.Array.QSort.Basic

/-! # `Array.qsort` sorts

Core proves nothing about `Array.qsort`; its workers `qsort.sort` and `qpartition.loop` are
private, so this file reads them with `import all`. For a transitive and asymmetric `lt`,
`qpartition` leaves the entries outside `[lo, hi]` alone, takes the entries of `[lo, hi]` from
`[lo, hi]`, puts entries `lt` the pivot before it and the others after it, and splits a range of
two or more entries strictly before its end (the median-of-three pivot is not `lt` the middle
entry). So `qsort.sort` sorts `[lo, hi]` (`Array.qsort_sorted`, `Array.qsort_sorted_nat`).
-/

@[expose] public section

namespace Array

/-- `bs` agrees with `as` outside `[lo, hi]` and takes its entries in `[lo, hi]` from there. -/
private structure SegOk {α : Type _} {n : Nat} (lo hi : Nat) (as bs : Vector α n) : Prop where
  out : ∀ j (h : j < n), (j < lo ∨ hi < j) → bs[j] = as[j]
  src : ∀ j (h : j < n), lo ≤ j → j ≤ hi →
    ∃ j' : Nat, ∃ h' : j' < n, lo ≤ j' ∧ j' ≤ hi ∧ bs[j] = as[j']

private theorem SegOk.refl {α : Type _} {n : Nat} (lo hi : Nat) (as : Vector α n) :
    SegOk lo hi as as :=
  ⟨fun _ _ _ => rfl, fun j h h₁ h₂ => ⟨j, h, h₁, h₂, rfl⟩⟩

private theorem SegOk.trans {α : Type _} {n : Nat} {lo hi : Nat} {as bs cs : Vector α n}
    (h₁ : SegOk lo hi as bs) (h₂ : SegOk lo hi bs cs) : SegOk lo hi as cs := by
  refine ⟨fun j h hj => (h₂.out j h hj).trans (h₁.out j h hj), fun j h hl hh => ?_⟩
  obtain ⟨j', h', hl', hh', e⟩ := h₂.src j h hl hh
  obtain ⟨j'', h'', hl'', hh'', e'⟩ := h₁.src j' h' hl' hh'
  exact ⟨j'', h'', hl'', hh'', e.trans e'⟩

private theorem SegOk.widen {α : Type _} {n : Nat} {lo hi lo' hi' : Nat} {as bs : Vector α n}
    (h : SegOk lo' hi' as bs) (hl : lo ≤ lo') (hh : hi' ≤ hi) : SegOk lo hi as bs := by
  refine ⟨fun j hj hout => h.out j hj (by omega), fun j hj h₁ h₂ => ?_⟩
  by_cases hin : lo' ≤ j ∧ j ≤ hi'
  · obtain ⟨j', h', hl', hh', e⟩ := h.src j hj hin.1 hin.2
    exact ⟨j', h', by omega, by omega, e⟩
  · exact ⟨j, hj, h₁, h₂, h.out j hj (by omega)⟩

private theorem SegOk.swap {α : Type _} {n : Nat} {lo hi : Nat} (as : Vector α n) (i k : Nat)
    (hi' : i < n) (hk : k < n) (h₁ : lo ≤ i) (h₂ : i ≤ hi) (h₃ : lo ≤ k) (h₄ : k ≤ hi) :
    SegOk lo hi as (as.swap i k hi' hk) := by
  refine ⟨fun j hj hout => ?_, fun j hj hl hh => ?_⟩
  · rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
  · rw [Vector.getElem_swap]
    split
    · exact ⟨k, hk, h₃, h₄, rfl⟩
    · split
      · exact ⟨i, hi', h₁, h₂, rfl⟩
      · exact ⟨j, hj, hl, hh, rfl⟩

private theorem SegOk.ite_swap {α : Type _} {n : Nat} {lo hi : Nat} (c : Prop) [Decidable c]
    (as : Vector α n) (i k : Nat) (hi' : i < n) (hk : k < n) (h₁ : lo ≤ i) (h₂ : i ≤ hi)
    (h₃ : lo ≤ k) (h₄ : k ≤ hi) :
    SegOk lo hi as (if c then as.swap i k hi' hk else as) := by
  split
  · exact SegOk.swap as i k hi' hk h₁ h₂ h₃ h₄
  · exact SegOk.refl lo hi as

private theorem qpartition_loop_spec {α : Type _} {n : Nat} (lt : α → α → Bool) (lo hi : Nat)
    (hhi : hi < n) (pivot : α) :
    ∀ (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi),
      (∀ j (h : j < n), lo ≤ j → j < i → lt as[j] pivot = true) →
      (∀ j (h : j < n), i ≤ j → j < k → lt as[j] pivot = false) →
      as[hi] = pivot →
      ∀ (m : {m : Nat // lo ≤ m ∧ m ≤ hi}) (bs : Vector α n),
      qpartition.loop lt lo hi hhi pivot as i k ilo ik w = (m, bs) →
      SegOk lo hi as bs ∧ bs[m.1]'(by have := m.2; omega) = pivot ∧
        (∀ j (h : j < n), lo ≤ j → j < m.1 → lt bs[j] pivot = true) ∧
        (∀ j (h : j < n), m.1 < j → j ≤ hi → lt bs[j] pivot = false) ∧
        ((i < k ∨ ∃ p : Nat, ∃ h : p < n, k ≤ p ∧ p < hi ∧ lt as[p] pivot = false) →
          m.1 < hi) := by
  intro as i k ilo ik w
  induction as, i, k, ilo, ik, w using qpartition.loop.induct lt lo hi hhi pivot with
  | case1 as i k ilo ik w h hlt ih =>
    intro hlo hmid hpiv m bs heq
    rw [qpartition.loop] at heq
    simp only [h, ↓reduceDIte, hlt, ↓reduceIte] at heq
    have hk : k < n := by omega
    obtain ⟨s, e, lo', hi', wit⟩ := ih
      (fun j hj h₁ h₂ => by
        rw [Vector.getElem_swap]
        split
        · next he => subst he; exact hlt
        · split
          · omega
          · exact hlo j hj h₁ (by omega))
      (fun j hj h₁ h₂ => by
        rw [Vector.getElem_swap]
        split
        · omega
        · split
          · exact hmid i (by omega) (Nat.le_refl _) (by omega)
          · exact hmid j hj (by omega) (by omega))
      (by rw [Vector.getElem_swap_of_ne (by omega) (by omega)]; exact hpiv) m bs heq
    refine ⟨(SegOk.swap as i k (by omega) hk ilo (by omega) (by omega) (by omega)).trans s, e,
      lo', hi', fun hw => wit ?_⟩
    rcases hw with hw | ⟨p, hp, h₁, h₂, h₃⟩
    · exact .inl (by omega)
    · by_cases hpk : p = k
      · subst hpk; rw [hlt] at h₃; cases h₃
      · by_cases hik : i < k
        · exact .inl (by omega)
        · refine .inr ⟨p, hp, by omega, h₂, ?_⟩
          rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
          exact h₃
  | case2 as i k ilo ik w h hlt ih =>
    intro hlo hmid hpiv m bs heq
    rw [qpartition.loop] at heq
    simp only [h, ↓reduceDIte, hlt, Bool.false_eq_true, ↓reduceIte] at heq
    obtain ⟨s, e, lo', hi', wit⟩ := ih hlo
      (fun j hj h₁ h₂ => by
        by_cases hjk : j = k
        · subst hjk; simpa using hlt
        · exact hmid j hj h₁ (by omega))
      hpiv m bs heq
    exact ⟨s, e, lo', hi', fun _ => wit (.inl (by omega))⟩
  | case3 as i k ilo ik w h =>
    intro hlo hmid hpiv m bs heq
    rw [qpartition.loop] at heq
    simp only [h, ↓reduceDIte, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    dsimp only
    have hk : k = hi := by omega
    subst hk
    refine ⟨SegOk.swap as i k (by omega) hhi ilo (by omega) (by omega) (by omega), ?_, ?_, ?_, ?_⟩
    · simp [hpiv]
    · intro j hj h₁ h₂
      rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      exact hlo j hj h₁ h₂
    · intro j hj h₁ h₂
      rw [Vector.getElem_swap]
      split
      · omega
      · split
        · exact hmid i (by omega) (Nat.le_refl _) (by omega)
        · exact hmid j hj (by omega) (by omega)
    · rintro (hw | ⟨p, hp, h₁, h₂, -⟩) <;> omega

private theorem qpartition_spec {α : Type _} {n : Nat} (lt : α → α → Bool)
    (hasymm : ∀ a b, lt a b = true → lt b a = false)
    (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n)
    (m : {m : Nat // lo ≤ m ∧ m ≤ hi}) (bs : Vector α n)
    (heq : qpartition as lt lo hi w hlo hhi = (m, bs)) :
    SegOk lo hi as bs ∧
      (∀ j (h : j < n), lo ≤ j → j < m.1 → lt bs[j] (bs[m.1]'(by have := m.2; omega)) = true) ∧
      (∀ j (h : j < n), m.1 < j → j ≤ hi → lt bs[j] (bs[m.1]'(by have := m.2; omega)) = false) ∧
      (lo < hi → m.1 < hi) := by
  unfold qpartition at heq
  dsimp only at heq
  have hm₁ : lo ≤ (lo + hi) / 2 := by omega
  have hm₂ : (lo + hi) / 2 ≤ hi := by omega
  generalize h₁ : (if lt as[(lo + hi) / 2] as[lo] = true then
    as.swap lo ((lo + hi) / 2) hlo (by omega) else as) = as₁ at heq
  generalize h₂ : (if lt as₁[hi] as₁[lo] = true then as₁.swap lo hi hlo hhi else as₁) = as₂ at heq
  generalize h₃ : (if lt as₂[(lo + hi) / 2] as₂[hi] = true then
    as₂.swap ((lo + hi) / 2) hi (by omega) hhi else as₂) = as₃ at heq
  have s₁ : SegOk lo hi as as₁ := h₁ ▸ SegOk.ite_swap _ _ _ _ _ _ (Nat.le_refl _) w hm₁ hm₂
  have s₂ : SegOk lo hi as₁ as₂ :=
    h₂ ▸ SegOk.ite_swap _ _ _ _ _ _ (Nat.le_refl _) w w (Nat.le_refl _)
  have s₃ : SegOk lo hi as₂ as₃ := h₃ ▸ SegOk.ite_swap _ _ _ _ _ _ hm₁ hm₂ w (Nat.le_refl _)
  -- the middle entry is not `lt` the pivot
  have hmp : lt as₃[(lo + hi) / 2] as₃[hi] = false := by
    subst h₃
    split
    · next hc =>
      rw [Vector.getElem_swap_left, Vector.getElem_swap_right]
      exact hasymm _ _ hc
    · next hc => simpa using hc
  obtain ⟨s, e, lo', hi', wit⟩ := qpartition_loop_spec lt lo hi hhi as₃[hi] as₃ lo lo
    (Nat.le_refl _) (Nat.le_refl _) w (fun _ _ _ _ => by omega) (fun _ _ _ _ => by omega) rfl m bs
    heq
  refine ⟨(s₁.trans s₂).trans (s₃.trans s), ?_, ?_, fun hlh => wit ?_⟩
  · intro j hj hl hh
    rw [e]; exact lo' j hj hl hh
  · intro j hj hl hh
    rw [e]; exact hi' j hj hl hh
  · exact .inr ⟨(lo + hi) / 2, by omega, hm₁, by omega, hmp⟩

/-- `bs` is sorted on `[lo, hi]`. -/
private def SortedOn {α : Type _} {n : Nat} (lt : α → α → Bool) (lo hi : Nat) (bs : Vector α n) :
    Prop :=
  ∀ i j (hi' : i < n) (hj : j < n), lo ≤ i → i < j → j ≤ hi → lt bs[j] bs[i] = false

private theorem qsort_sort_spec {α : Type _} (lt : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) {n : Nat} (as : Vector α n)
    (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    SegOk lo hi as (qsort.sort lt as lo hi w hlo hhi) ∧
      SortedOn lt lo hi (qsort.sort lt as lo hi w hlo hhi) := by
  induction as, lo, hi, w, hlo, hhi using qsort.sort.induct lt with
  | case1 as lo hi w hlo hhi h mid hmid as' hp hge =>
    rw [qsort.sort]
    simp only [h, ↓reduceDIte, hp, hge]
    have := (qpartition_spec lt hasymm as lo hi w hlo hhi _ _ hp).2.2.2 h
    simp only at this
    omega
  | case2 as lo hi w hlo hhi h mid hmid as' hp hge ih₁ _ ih₂ =>
    rw [qsort.sort]
    simp only [h, ↓reduceDIte, hp, hge]
    obtain ⟨s, plo, phi, -⟩ := qpartition_spec lt hasymm as lo hi w hlo hhi _ _ hp
    simp only at plo phi
    obtain ⟨s₁, o₁⟩ := ih₁
    obtain ⟨s₂, o₂⟩ := ih₂
    generalize qsort.sort lt as' lo mid _ _ _ = bs₁ at s₁ o₁ s₂ o₂
    generalize qsort.sort lt bs₁ (mid + 1) hi _ _ _ = bs₂ at s₂ o₂
    have hmn : mid < n := by omega
    -- entries of `[lo, mid]` are `lt` the pivot or the pivot; those of `(mid, hi]` are not `lt` it
    have left : ∀ j (hj : j < n), lo ≤ j → j ≤ mid →
        lt bs₂[j] as'[mid] = true ∨ bs₂[j] = as'[mid] := by
      intro j hj h₁ h₂
      rw [s₂.out j hj (by omega)]
      obtain ⟨j', hj', h₁', h₂', e⟩ := s₁.src j hj h₁ h₂
      rw [e]
      by_cases hjm : j' = mid
      · subst hjm; exact .inr rfl
      · exact .inl (plo j' hj' h₁' (by omega))
    have right : ∀ j (hj : j < n), mid < j → j ≤ hi → lt bs₂[j] as'[mid] = false := by
      intro j hj h₁ h₂
      obtain ⟨j', hj', h₁', h₂', e⟩ := s₂.src j hj (by omega) h₂
      rw [e, s₁.out j' hj' (by omega)]
      exact phi j' hj' (by omega) h₂'
    refine ⟨(s.trans (s₁.widen (Nat.le_refl _) (by omega))).trans
      (s₂.widen (by omega) (Nat.le_refl _)),
      fun i j hi' hj h₁ h₂ h₃ => ?_⟩
    by_cases hjm : j ≤ mid
    · rw [s₂.out j hj (by omega), s₂.out i hi' (by omega)]
      exact o₁ i j hi' hj h₁ h₂ hjm
    · by_cases him : mid < i
      · exact o₂ i j hi' hj him h₂ h₃
      · have hr := right j hj (by omega) h₃
        rcases left i hi' h₁ (by omega) with hl | hl
        · cases hc : lt bs₂[j] bs₂[i]
          · rfl
          · rw [htrans _ _ _ hc hl] at hr; cases hr
        · rw [hl]; exact hr
  | case3 as lo hi w hlo hhi h =>
    rw [qsort.sort]
    simp only [h, ↓reduceDIte]
    exact ⟨SegOk.refl lo hi as, fun _ _ _ _ _ _ _ => by omega⟩

/-- For a transitive and asymmetric `lt`, `Array.qsort` sorts: no later entry is `lt` an
earlier one. -/
theorem qsort_sorted {α : Type _} (as : Array α) (lt : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) :
    ∀ i j (hi : i < (as.qsort lt).size) (hj : j < (as.qsort lt).size), i < j →
      lt (as.qsort lt)[j] (as.qsort lt)[i] = false := by
  intro i j hi hj hij
  unfold qsort
  split
  · next h => simp [qsort, h] at hj
  · next h =>
    simp only [Nat.zero_le, Nat.min_eq_left, Nat.le_refl, Nat.min_eq_left, Nat.max_eq_right] at *
    have hs : (qsort.sort lt as.toVector 0 (as.size - 1)).toArray.size = as.size := by simp
    have := (qsort_sort_spec lt htrans hasymm as.toVector 0 (as.size - 1) (by omega) (by omega)
      (by omega)).2 i j (by simp [qsort, h] at hi; omega) (by simp [qsort, h] at hj; omega)
      (by omega) hij (by simp [qsort, h] at hj; omega)
    simpa using this

/-- `Array.qsort` with `<` sorts an array of naturals. -/
theorem qsort_sorted_nat (as : Array Nat) : (as.qsort (· < ·)).toList.Pairwise (· ≤ ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := qsort_sorted as (fun a b => decide (a < b))
    (fun a b c h₁ h₂ => by simp at *; omega) (fun a b h => by simp at *; omega)
    i j (by simpa using hi) (by simpa using hj) hij
  simp only [decide_eq_false_iff_not, Nat.not_lt] at this
  simpa using this

end Array
