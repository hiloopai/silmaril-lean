module

public import Silmaril.Data.BoundaryTag.Defs
public import Silmaril.Data.Cells.Thms

/-!
# Header runs with boundary tags: split and merge

`run` splits along `++` (`run_append`); the separation of the old fragment (with the fresh
header of a split) gives every apartness the store rule `Silmaril.Data.Cell.holds_storeAll` needs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Data.BoundaryTag

open Silmaril.Data

theorem lastFree_cons (pf : Bool) (b : Blk) (bs : List Blk) :
    lastFree pf (b :: bs) = lastFree b.free bs := by
  cases bs with
  | nil => simp [lastFree]
  | cons c cs => simp [lastFree, List.getLast?_cons_cons, List.getLast?_cons]

theorem run_append (T : Tag) : ∀ (pf : Bool) (l₁ l₂ : List Blk),
    run T pf (l₁ ++ l₂) = run T pf l₁ ++ run T (lastFree pf l₁) l₂
  | pf, [], l₂ => by simp [run, lastFree]
  | pf, b :: bs, l₂ => by
    simp only [List.cons_append, run, List.append_assoc, run_append T b.free bs l₂, lastFree_cons]

theorem Cell.Apart.addr_ne {c d : Cell} (h : c.Apart d) (hc : 0 < c.width) (hd : 0 < d.width) :
    c.addr ≠ d.addr := fun e => h c.addr (Nat.le_refl _) (by omega) (by omega) (by omega)

/-- Apartness from a separated `A ++ B`. -/
theorem sep_app_apart {A B : Frag} (h : Frag.Sep (A ++ B)) {c d : Cell} (hc : c ∈ A) (hd : d ∈ B) :
    c.Apart d := (Frag.sep_append.1 h).2.2 c hc d hd

theorem tagSplit : Task.seplist.tagSplit := by
  intro T v pf pre post b s₁ hws hf hs1 hs1b hfit hwr hS
  obtain ⟨ba, bsz, bf⟩ := b
  simp only at hs1b hfit hwr hS hf ⊢
  rw [run_append] at hf hS ⊢
  generalize lastFree pf pre = p' at hf hS ⊢
  generalize run T pf pre = A at hf hS ⊢
  have hfl : (if p' = true then 0 else T.prevInuse) ≤ T.prevInuse := by split <;> omega
  cases bf with
  | false =>
    simp only [run, ↓reduceIte, Bool.false_eq_true, List.nil_append, List.append_nil] at hf hS ⊢
    generalize run T false post = P at hf hS ⊢
    have hb : (⟨ba + T.sizeOff, T.ws, bsz + if p' = true then 0 else T.prevInuse⟩ : Cell) ∈
        A ++ _ :: P := List.mem_append_right _ (List.mem_cons_self ..)
    rw [List.append_assoc] at hS
    have hS1 := (Frag.sep_append.1 hS).2.1
    have hbP := Frag.sep_cons.1 (Frag.sep_append.1 hS1).1
    have hbfr := sep_app_apart hS1 (List.mem_cons_self ..) (List.mem_singleton_self _)
    intro c hc
    refine Cell.holds_storeAll ?_ ?_ ?_
    · intro d hd
      simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨by simp only; omega, (hf _ hb).2⟩
      · exact ⟨by simp only; omega, hwr⟩
    · exact List.pairwise_pair.2 (hbfr.of_eq rfl rfl rfl rfl)
    · simp only [List.mem_append, List.mem_cons] at hc
      rcases hc with hc | rfl | rfl | hc
      · refine .inr ⟨hf c (List.mem_append_left _ hc), fun d hd => ?_⟩
        simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact (sep_app_apart hS hc (List.mem_append_left _ (List.mem_cons_self ..))).of_eq rfl rfl rfl rfl
        · exact (sep_app_apart hS hc (List.mem_append_right _ (List.mem_singleton_self _))).of_eq
            rfl rfl rfl rfl
      · exact .inl (by simp)
      · exact .inl (by simp)
      · refine .inr ⟨hf c (List.mem_append_right _ (List.mem_cons_of_mem _ hc)), fun d hd => ?_⟩
        simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact (hbP.2 c hc).symm.of_eq rfl rfl rfl rfl
        · exact (sep_app_apart hS1 (List.mem_cons_of_mem _ hc) (List.mem_singleton_self _)).of_eq
            rfl rfl rfl rfl
  | true =>
    have e : ba + s₁ + (bsz - s₁) = ba + bsz := by omega
    simp only [run, ↓reduceIte, Bool.false_eq_true, List.nil_append, List.singleton_append, e] at hf hS ⊢
    generalize run T true post = P at hf hS ⊢
    have hbH := hf ⟨ba + T.sizeOff, T.ws, bsz + if p' = true then 0 else T.prevInuse⟩ (by simp)
    have htH := hf ⟨ba + bsz + T.tagOff, T.ws, bsz⟩ (by simp)
    rw [List.append_assoc] at hS
    have hS1 := (Frag.sep_append.1 hS).2.1
    have hbP := Frag.sep_cons.1 (Frag.sep_append.1 hS1).1
    have htP := Frag.sep_cons.1 hbP.1
    have hbfr := sep_app_apart hS1 (List.mem_cons_self ..) (List.mem_singleton_self _)
    have htfr := sep_app_apart hS1 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (List.mem_singleton_self _)
    have hbt := hbP.2 _ (List.mem_cons_self ..)
    intro c hc
    refine Cell.holds_storeAll ?_ ?_ ?_
    · intro d hd
      simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact ⟨by simp only; omega, hbH.2⟩
      · exact ⟨by simp only; omega, hwr⟩
      · exact ⟨by simp only; omega, htH.2⟩
    · simp only [List.cons_append, List.nil_append, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      exact ⟨⟨hbfr.of_eq rfl rfl rfl rfl, hbt.of_eq rfl rfl rfl rfl⟩,
        htfr.symm.of_eq rfl rfl rfl rfl, fun _ h => h.elim⟩
    · simp only [List.mem_append, List.mem_cons] at hc
      rcases hc with hc | rfl | rfl | rfl | hc
      · refine .inr ⟨hf c (List.mem_append_left _ hc), fun d hd => ?_⟩
        simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl
        · exact (sep_app_apart hS hc (List.mem_append_left _ (List.mem_cons_self ..))).of_eq rfl rfl rfl rfl
        · exact (sep_app_apart hS hc (List.mem_append_right _ (List.mem_singleton_self _))).of_eq
            rfl rfl rfl rfl
        · exact (sep_app_apart hS hc (List.mem_append_left _
            (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).of_eq rfl rfl rfl rfl
      · exact .inl (by simp)
      · exact .inl (by simp)
      · exact .inl (by simp)
      · refine .inr ⟨hf c (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))),
          fun d hd => ?_⟩
        simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl
        · exact (hbP.2 c (List.mem_cons_of_mem _ hc)).symm.of_eq rfl rfl rfl rfl
        · exact (sep_app_apart hS1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
            (List.mem_singleton_self _)).of_eq rfl rfl rfl rfl
        · exact (htP.2 c hc).symm.of_eq rfl rfl rfl rfl

theorem tagMerge : Task.seplist.tagMerge := by
  intro T v pf pre post b₁ b₂ f hws hf hadj hff hfit hS
  obtain ⟨a1, s1, f1⟩ := b₁
  obtain ⟨a2, s2, f2⟩ := b₂
  simp only at hadj hff hfit ⊢
  subst hadj
  subst hff
  rw [run_append] at hf hS ⊢
  generalize lastFree pf pre = p' at hf hS ⊢
  generalize run T pf pre = A at hf hS ⊢
  have hfl : (if p' = true then 0 else T.prevInuse) ≤ T.prevInuse := by split <;> omega
  simp only [run, List.cons_append, List.append_assoc] at hf hS ⊢
  generalize (if f1 = true then [(⟨a1 + s1 + T.tagOff, T.ws, s1⟩ : Cell)] else []) = tb1 at hf hS
  have hb1H := hf ⟨a1 + T.sizeOff, T.ws, s1 + if p' = true then 0 else T.prevInuse⟩ (by simp)
  cases f with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil] at hf hS ⊢
    generalize run T false post = P at hf hS ⊢
    obtain ⟨_, hSR, hAR⟩ := Frag.sep_append.1 hS
    obtain ⟨hS2, hb1R⟩ := Frag.sep_cons.1 hSR
    obtain ⟨_, hS3, _⟩ := Frag.sep_append.1 hS2
    obtain ⟨hS4, _⟩ := Frag.sep_cons.1 hS3
    intro c hc
    refine Cell.holds_storeAll ?_ (List.pairwise_singleton _ _) ?_
    · intro d hd
      simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_singleton] at hd; subst hd
      exact ⟨by simp only; omega, hb1H.2⟩
    · simp only [List.mem_append, List.mem_cons] at hc
      rcases hc with hc | rfl | hc
      · refine .inr ⟨hf c (List.mem_append_left _ hc), fun d hd => ?_⟩
        simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_singleton] at hd; subst hd
        exact (hAR c hc _ (List.mem_cons_self ..)).of_eq rfl rfl rfl rfl
      · exact .inl (by simp)
      · refine .inr ⟨hf c (by simp [hc]), fun d hd => ?_⟩
        simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_singleton] at hd; subst hd
        exact (hb1R c (by simp [hc])).symm.of_eq rfl rfl rfl rfl
  | true =>
    simp only [↓reduceIte, List.singleton_append, List.cons_append, Nat.add_assoc] at hf hS hfit hb1H ⊢
    generalize run T true post = P at hf hS ⊢
    obtain ⟨_, hSR, hAR⟩ := Frag.sep_append.1 hS
    obtain ⟨hS2, hb1R⟩ := Frag.sep_cons.1 hSR
    obtain ⟨_, hS3, _⟩ := Frag.sep_append.1 hS2
    obtain ⟨hS4, _⟩ := Frag.sep_cons.1 hS3
    have htH := hf ⟨a1 + (s1 + (s2 + T.tagOff)), T.ws, s2⟩ (by simp)
    obtain ⟨_, htP⟩ := Frag.sep_cons.1 hS4
    have hbt := hb1R ⟨a1 + (s1 + (s2 + T.tagOff)), T.ws, s2⟩ (by simp)
    intro c hc
    refine Cell.holds_storeAll ?_ (List.pairwise_pair.2 (hbt.of_eq rfl rfl rfl rfl)) ?_
    · intro d hd
      simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨by simp only; omega, hb1H.2⟩
      · exact ⟨by simp only; omega, htH.2⟩
    · simp only [List.mem_append, List.mem_cons] at hc
      rcases hc with hc | rfl | rfl | hc
      · refine .inr ⟨hf c (List.mem_append_left _ hc), fun d hd => ?_⟩
        simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact (hAR c hc _ (List.mem_cons_self ..)).of_eq rfl rfl rfl rfl
        · exact (hAR c hc ⟨a1 + (s1 + (s2 + T.tagOff)), T.ws, s2⟩ (by simp)).of_eq rfl rfl rfl rfl
      · exact .inl (by simp)
      · exact .inl (by simp)
      · replace hc : c ∈ P := by simpa using hc
        refine .inr ⟨hf c (by simp [hc]), fun d hd => ?_⟩
        simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact (hb1R c (by simp [hc])).symm.of_eq rfl rfl rfl rfl
        · exact (htP c (by simpa using hc)).symm.of_eq rfl rfl rfl rfl

end Silmaril.Data.BoundaryTag
