module

public import Silmaril.Semantics.Accept.Automata.Defs
public import Silmaril.Semantics.Accept.Thms

/-! # Proofs: automata as acceptor presentations -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Automata

open Silmaril.Accept Silmaril.Accept.Automata Cslib.Automata

universe u v

variable {α : Type u} {σ : Type v}

theorem accepts_eq_acceptsSome_nfaRun (M : NFA α σ) :
    M.accepts = acceptsSome (nfaRun M) M.accept := by
  ext w
  exact ⟨fun ⟨s, h₁, h₂⟩ => ⟨s, h₂, h₁⟩,
    fun ⟨s, h₁, h₂⟩ => ⟨s, h₂, h₁⟩⟩

theorem accepts_eq_acceptsSome_εnfaRun (M : εNFA α σ) :
    M.accepts = acceptsSome (εnfaRun M) M.accept := by
  ext w
  exact ⟨fun ⟨s, h₁, h₂⟩ => ⟨s, h₂, h₁⟩,
    fun ⟨s, h₁, h₂⟩ => ⟨s, h₂, h₁⟩⟩

theorem nfaRun_toNFA (M : DFA α σ) : nfaRun M.toNFA = dfaRun M := by
  funext w
  simp only [nfaRun, dfaRun, detRun, NFA.eval, DFA.toNFA_start, DFA.toNFA_evalFrom_match]
  rfl

theorem nfaRun_of_start_eq_empty (M : NFA α σ) (h : M.start = ∅) (w : List α) :
    nfaRun M w = ∅ := by
  change M.evalFrom M.start w = ∅
  rw [h]
  induction w with
  | nil => rfl
  | cons a w ih => rw [NFA.evalFrom_cons, NFA.stepSet_empty, ih]

theorem acceptsAll_nfaRun_ne_accepts_of_start_eq_empty (M : NFA α σ) (h : M.start = ∅) :
    acceptsAll (nfaRun M) M.accept ≠ M.accepts := by
  intro he
  have hall : [] ∈ acceptsAll (nfaRun M) M.accept := by
    intro o ho
    rw [nfaRun_of_start_eq_empty M h] at ho
    exact absurd ho (Set.notMem_empty o)
  rw [he, accepts_eq_acceptsSome_nfaRun] at hall
  exact not_mem_acceptsSome_of_eq_empty (nfaRun_of_start_eq_empty M h []) hall

theorem mem_evalFrom_iff_mTr (M : NFA α σ) (S : Set σ) (w : List α) (t : σ) :
    t ∈ M.evalFrom S w ↔ ∃ s ∈ S, (toCslibNA M).MTr s w t := by
  induction w generalizing S with
  | nil => simp
  | cons a w ih =>
    rw [NFA.evalFrom_cons, ih]
    simp only [NFA.mem_stepSet, Cslib.LTS.MTr.cons_iff]
    constructor
    · rintro ⟨u, ⟨s, hs, hu⟩, hmtr⟩
      exact ⟨s, hs, u, hu, hmtr⟩
    · rintro ⟨s, hs, u, hu, hmtr⟩
      exact ⟨u, ⟨s, hs, hu⟩, hmtr⟩

theorem language_toCslibNA (M : NFA α σ) :
    Acceptor.language (toCslibNA M) = M.accepts := by
  ext w
  rw [Acceptor.mem_language, NFA.mem_accepts]
  change (∃ s ∈ M.start, ∃ s' ∈ M.accept, (toCslibNA M).MTr s w s') ↔ _
  simp only [mem_evalFrom_iff_mTr]
  constructor
  · rintro ⟨s, hs, t, ht, h⟩
    exact ⟨t, ht, s, hs, h⟩
  · rintro ⟨t, ht, s, hs, h⟩
    exact ⟨s, hs, t, ht, h⟩

/-! ## The digits DFA -/

theorem evalFrom_dead (w : List UInt8) : digitsDFA.evalFrom .dead w = .dead := by
  induction w with
  | nil => rfl
  | cons b w ih => exact ih

theorem evalFrom_digits (w : List UInt8) :
    digitsDFA.evalFrom .digits w = if w.all isDigit then .digits else .dead := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [DFA.evalFrom_cons, List.all_cons]
    by_cases hb : isDigit b = true
    · simp only [digitsDFA, hb, ite_true, Bool.true_and] at ih ⊢
      exact ih
    · simp only [digitsDFA, hb, Bool.false_and, Bool.false_eq_true, ite_false]
      exact evalFrom_dead w

theorem mem_digitsLang {w : List UInt8} :
    w ∈ digitsLang ↔ w ≠ [] ∧ ∀ b ∈ w, isDigit b = true := Iff.rfl

theorem accepts_digitsDFA : digitsDFA.accepts = digitsLang := by
  ext w
  rw [DFA.mem_accepts]
  cases w with
  | nil => simp [digitsDFA, mem_digitsLang, DFA.eval]
  | cons b w =>
    change digitsDFA.evalFrom (digitsDFA.step .start b) w = .digits ↔ _
    by_cases hb : isDigit b = true
    · simp only [digitsDFA, hb, ite_true]
      rw [← digitsDFA.eq_def, evalFrom_digits]
      simp [mem_digitsLang, hb, List.all_eq_true]
    · simp only [digitsDFA, hb, Bool.false_eq_true, ite_false]
      rw [← digitsDFA.eq_def, evalFrom_dead]
      simp [mem_digitsLang, hb]

end Silmaril.Proofs.Semantics.Accept.Automata
