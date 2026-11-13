module

public import Silmaril.Automata.Decide.Defs

/-!
# Decision procedures for finite machines: proofs

For `Silmaril.Automata.Decide.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Automata

open Silmaril.Automata

theorem iterate_fix_of_fix {α : Type} {F : α → α} {x : α} (h : F x = x) (n : Nat) :
    F^[n] x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, h, ih]

theorem iterate_fix_of_deflationary {α : Type} [Fintype α] [DecidableEq α]
    (F : Finset α → Finset α) (hF : ∀ X, F X ⊆ X) (X : Finset α) :
    F (F^[Fintype.card α] X) = F^[Fintype.card α] X := by
  have claim : ∀ n, F (F^[n] X) = F^[n] X ∨ (F^[n] X).card + n ≤ X.card := by
    intro n
    induction n with
    | zero => right; simp
    | succ n ih =>
      by_cases h0 : F (F^[n + 1] X) = F^[n + 1] X
      · exact Or.inl h0
      · right
        have hs : F^[n + 1] X = F (F^[n] X) := Function.iterate_succ_apply' F n X
        by_cases h1 : F (F^[n] X) = F^[n] X
        · exfalso; apply h0; rw [hs, h1, h1]
        · rcases ih with h | h
          · exact absurd h h1
          · have hlt : (F (F^[n] X)).card < (F^[n] X).card :=
              Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hF _, h1⟩)
            rw [hs]; omega
  rcases claim (Fintype.card α) with h | h
  · exact h
  · have hX : X.card ≤ Fintype.card α := Finset.card_le_univ X
    have h0 : F^[Fintype.card α] X = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [h0]; exact Finset.subset_empty.mp (hF ∅)

theorem iterate_fix_of_inflationary {α : Type} [Fintype α] [DecidableEq α]
    (F : Finset α → Finset α) (hF : ∀ X, X ⊆ F X) (X : Finset α) :
    F (F^[Fintype.card α] X) = F^[Fintype.card α] X := by
  have claim : ∀ n, F (F^[n] X) = F^[n] X ∨ X.card + n ≤ (F^[n] X).card := by
    intro n
    induction n with
    | zero => right; simp
    | succ n ih =>
      by_cases h0 : F (F^[n + 1] X) = F^[n + 1] X
      · exact Or.inl h0
      · right
        have hs : F^[n + 1] X = F (F^[n] X) := Function.iterate_succ_apply' F n X
        by_cases h1 : F (F^[n] X) = F^[n] X
        · exfalso; apply h0; rw [hs, h1, h1]
        · rcases ih with h | h
          · exact absurd h h1
          · have hlt : (F^[n] X).card < (F (F^[n] X)).card :=
              Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hF _, Ne.symm h1⟩)
            rw [hs]; omega
  rcases claim (Fintype.card α) with h | h
  · exact h
  · have hY : (F^[Fintype.card α] X).card ≤ Fintype.card α := Finset.card_le_univ _
    have hu : F^[Fintype.card α] X = Finset.univ :=
      Finset.eq_univ_of_card _ (by omega)
    rw [hu]; exact Finset.eq_univ_iff_forall.mpr (fun a => hF _ (Finset.mem_univ a))

theorem subset_iterate_of_inflationary {α : Type} {F : Finset α → Finset α}
    (hF : ∀ X, X ⊆ F X) (X : Finset α) (n : Nat) : X ⊆ F^[n] X := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.trans (hF _)

section Reach

variable {S L : Type} [Fintype S] [Fintype L] [DecidableEq S]

omit [Fintype S] in
theorem mem_reachStep {M : NMachine S L} {P : L → Bool} {X : Finset S} {b : S} :
    b ∈ M.reachStep P X ↔ b ∈ X ∨ ∃ s ∈ X, ∃ l, P l = true ∧ b ∈ M.step s l := by
  simp [NMachine.reachStep]

omit [Fintype S] in
theorem reachStep_inflationary (M : NMachine S L) (P : L → Bool) (X : Finset S) :
    X ⊆ M.reachStep P X := Finset.subset_union_left

omit [Fintype S] in
theorem reach_sound (M : NMachine S L) (P : L → Bool) (a : S) (n : Nat) (b : S)
    (hb : b ∈ (M.reachStep P)^[n] {a}) : ReachVia M.toLTS (fun l => P l = true) a b := by
  induction n generalizing b with
  | zero => simp at hb; subst hb; exact Relation.ReflTransGen.refl
  | succ n ih =>
    rw [Function.iterate_succ_apply', mem_reachStep] at hb
    rcases hb with hb | ⟨s, hs, l, hl, hst⟩
    · exact ih b hb
    · exact Relation.ReflTransGen.tail (ih s hs) ⟨l, hl, hst⟩

theorem mem_reachSetN (M : NMachine S L) (P : L → Bool) (a b : S) :
    b ∈ M.reachSet P a ↔ ReachVia M.toLTS (fun l => P l = true) a b := by
  constructor
  · exact reach_sound M P a _ b
  · intro h
    have hfix := iterate_fix_of_inflationary (M.reachStep P) (reachStep_inflationary M P) {a}
    induction h with
    | refl =>
      exact subset_iterate_of_inflationary (reachStep_inflationary M P) {a} _
        (Finset.mem_singleton_self a)
    | tail _ hst ih =>
      obtain ⟨l, hl, hst⟩ := hst
      unfold NMachine.reachSet
      rw [← hfix, mem_reachStep]
      exact Or.inr ⟨_, ih, l, hl, hst⟩

theorem mem_reachSet (M : DMachine S L) (P : L → Bool) (a b : S) :
    b ∈ reachSet M P a ↔ ReachVia M.toLTS (fun l => P l = true) a b := by
  rw [← M.toN_toLTS]; exact mem_reachSetN M.toN P a b

end Reach

section Sim

variable {S T L : Type} [Fintype S] [Fintype T] [Fintype L] [DecidableEq S] [DecidableEq T]

omit [Fintype T] in
theorem simStep_deflationary (M : NMachine S L) (N : NMachine T L) (R : Finset (S × T)) :
    M.simStep N R ⊆ R := Finset.filter_subset _ _

theorem simSet_fix (M : NMachine S L) (N : NMachine T L) :
    M.simStep N (M.simSet N) = M.simSet N :=
  iterate_fix_of_deflationary _ (simStep_deflationary M N) _

theorem mem_simSetN (M : NMachine S L) (N : NMachine T L) (s : S) (t : T) :
    (s, t) ∈ M.simSet N ↔ Cslib.LTS.Similarity M.toLTS N.toLTS s t := by
  constructor
  · intro h
    refine ⟨fun s t => (s, t) ∈ M.simSet N, h, ?_⟩
    intro s₁ s₂ hr μ s₁' htr
    rw [← simSet_fix] at hr
    simp only [NMachine.simStep, NMachine.simOK, Finset.mem_filter, decide_eq_true_eq] at hr
    obtain ⟨t', ht', hm⟩ := hr.2 μ s₁' htr
    exact ⟨t', ht', hm⟩
  · rintro ⟨r, hr, hsim⟩
    have key : ∀ n, ∀ p : S × T, r p.1 p.2 → p ∈ (M.simStep N)^[n] Finset.univ := by
      intro n
      induction n with
      | zero => intro p _; exact Finset.mem_univ p
      | succ n ih =>
        intro p hp
        rw [Function.iterate_succ_apply']
        simp only [NMachine.simStep, NMachine.simOK, Finset.mem_filter, decide_eq_true_eq]
        refine ⟨ih p hp, fun l s' hs' => ?_⟩
        obtain ⟨t', ht', hr'⟩ := hsim hp l s' hs'
        exact ⟨t', ht', ih (s', t') hr'⟩
    exact key _ (s, t) hr

theorem mem_simSet (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) :
    (s, t) ∈ simSet M N ↔ Cslib.LTS.Similarity M.toLTS N.toLTS s t := by
  rw [← M.toN_toLTS, ← N.toN_toLTS]; exact mem_simSetN M.toN N.toN s t

theorem bisimStep_deflationary (M : NMachine S L) (N : NMachine T L) (R : Finset (S × T)) :
    M.bisimStep N R ⊆ R := Finset.filter_subset _ _

theorem bisimSet_fix (M : NMachine S L) (N : NMachine T L) :
    M.bisimStep N (M.bisimSet N) = M.bisimSet N :=
  iterate_fix_of_deflationary _ (bisimStep_deflationary M N) _

theorem mem_bisimSetN (M : NMachine S L) (N : NMachine T L) (s : S) (t : T) :
    (s, t) ∈ M.bisimSet N ↔ Cslib.LTS.Bisimilarity M.toLTS N.toLTS s t := by
  constructor
  · intro h
    refine ⟨fun s t => (s, t) ∈ M.bisimSet N, h, ?_⟩
    intro s₁ s₂ hr μ
    rw [← bisimSet_fix] at hr
    simp only [NMachine.bisimStep, NMachine.bisimOK, Finset.mem_filter, decide_eq_true_eq] at hr
    exact ⟨fun s₁' htr => hr.2 μ |>.1 s₁' htr, fun s₂' htr => hr.2 μ |>.2 s₂' htr⟩
  · rintro ⟨r, hr, hsim⟩
    have key : ∀ n, ∀ p : S × T, r p.1 p.2 → p ∈ (M.bisimStep N)^[n] Finset.univ := by
      intro n
      induction n with
      | zero => intro p _; exact Finset.mem_univ p
      | succ n ih =>
        intro p hp
        rw [Function.iterate_succ_apply']
        simp only [NMachine.bisimStep, NMachine.bisimOK, Finset.mem_filter, decide_eq_true_eq]
        refine ⟨ih p hp, fun l => ⟨fun s' hs' => ?_, fun t' ht' => ?_⟩⟩
        · obtain ⟨t', ht', hr'⟩ := (hsim hp l).1 s' hs'
          exact ⟨t', ht', ih (s', t') hr'⟩
        · obtain ⟨s', hs', hr'⟩ := (hsim hp l).2 t' ht'
          exact ⟨s', hs', ih (s', t') hr'⟩
    exact key _ (s, t) hr

theorem mem_bisimSet (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) :
    (s, t) ∈ bisimSet M N ↔ Cslib.LTS.Bisimilarity M.toLTS N.toLTS s t := by
  rw [← M.toN_toLTS, ← N.toN_toLTS]; exact mem_bisimSetN M.toN N.toN s t

end Sim

end Silmaril.Proofs.Automata
