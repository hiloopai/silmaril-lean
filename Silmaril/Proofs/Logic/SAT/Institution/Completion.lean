module

public import Silmaril.Logic.SAT.Institution.Defs
import Silmaril.Proofs.Logic.SAT.Institution.Evaluation
import Silmaril.Logic.ManyValued.Thms

public section

namespace Silmaril.Proofs.Logic.SAT.Institution

open Silmaril.Logic.SAT.Institution Silmaril.Logic.ManyValued

universe u v
variable {A : Type u} {B : Type v}

theorem exists_completion (v : PartialValuation A) : ∃ t, Completes v t := by
  refine ⟨fun a => (v a).getD false, ?_⟩
  intro a b h
  simp [h]

theorem completionEvidence_support_iff (v : PartialValuation A) (F : Problem A) :
    (F.completionEvidence v).support = true ↔ ∀ t, Completes v t → F.eval t = true := by
  simp [Problem.completionEvidence, FDE.support_ofBits]

theorem completionEvidence_refute_iff (v : PartialValuation A) (F : Problem A) :
    (F.completionEvidence v).refute = true ↔ ∀ t, Completes v t → F.eval t = false := by
  simp [Problem.completionEvidence, FDE.refute_ofBits]

theorem completionEvidence_consistent (v : PartialValuation A) (F : Problem A) :
    ¬ ((F.completionEvidence v).support = true ∧ (F.completionEvidence v).refute = true) := by
  obtain ⟨t, ht⟩ := exists_completion v
  rintro ⟨pos, neg⟩
  have hp := (completionEvidence_support_iff v F).1 pos t ht
  have hn := (completionEvidence_refute_iff v F).1 neg t ht
  exact Bool.noConfusion (hp.symm.trans hn)

theorem completionEvidence_eq_ofK3_superEval (v : PartialValuation A) (F : Problem A) :
    F.completionEvidence v = (F.superEvalK3 v).toFDE := by
  cases h : (F.completionEvidence v).toK3? with
  | none =>
    have hb := (FDE.toK3?_eq_none_iff _).1 h
    exact (completionEvidence_consistent v F (by rw [hb]; exact ⟨rfl, rfl⟩)).elim
  | some k =>
    unfold Problem.superEvalK3
    rw [h]
    exact ((FDE.toK3?_eq_some_iff _ _).1 h).symm

theorem superEval_eq_some (v : PartialValuation A) (F : Problem A) (b : Bool) :
    F.superEval v = some b ↔ ∀ t, Completes v t → F.eval t = b := by
  change (F.superEvalK3 v).toOptionBool = some b ↔ _
  cases b
  · rw [← completionEvidence_refute_iff, completionEvidence_eq_ofK3_superEval]
    cases F.superEvalK3 v <;> decide
  · rw [← completionEvidence_support_iff, completionEvidence_eq_ofK3_superEval]
    cases F.superEvalK3 v <;> decide

theorem toOptionBool_eq_some_iff (k : K3) (b : Bool) :
    k.toOptionBool = some b ↔ k = K3.ofBool b := by
  cases k <;> cases b <;> decide

theorem superEval_eq_none (v : PartialValuation A) (F : Problem A) :
    F.superEval v = none ↔
      (∃ t, Completes v t ∧ F.eval t = true) ∧ (∃ t, Completes v t ∧ F.eval t = false) := by
  classical
  have witness (b : Bool) : (¬ ∀ t, Completes v t → F.eval t = b) ↔
      ∃ t, Completes v t ∧ F.eval t = !b := by
    simp only [Classical.not_forall]
    apply exists_congr
    intro t
    cases b <;> cases F.eval t <;> simp
  have ht := witness false
  have hf := witness true
  simp only [Bool.not_false] at ht
  simp only [Bool.not_true] at hf
  rw [← ht, ← hf, ← superEval_eq_some, ← superEval_eq_some]
  rcases F.superEval v with _ | (_ | _) <;> simp

theorem superEval_total (t : TotalValuation A) (F : Problem A) :
    F.superEval (some ∘ t) = some (F.eval t) := by
  apply (superEval_eq_some _ _ _).2
  intro s hs
  have h : s = t := funext fun a => hs a (t a) rfl
  rw [h]

theorem evalK3_informationLE_superEval (v : PartialValuation A) (F : Problem A) :
    (⟨F.evalK3Partial v⟩ : K3.Information) ≤ ⟨F.superEvalK3 v⟩ := by
  apply (K3.Information.le_iff_toOptionBool _ _).2
  intro b hb
  apply (superEval_eq_some _ _ _).2
  intro t ht
  have hv (a : A) : (⟨v.toK3 a⟩ : K3.Information) ≤ ⟨K3.ofBool (t a)⟩ := by
    apply (K3.Information.le_iff_toOptionBool _ _).2
    intro c hc
    change (K3.ofOptionBool (v a)).toOptionBool = some c at hc
    rw [K3.toOptionBool_ofOptionBool] at hc
    change (K3.ofOptionBool (some (t a))).toOptionBool = some c
    rw [K3.toOptionBool_ofOptionBool, ht a c hc]
  have h := evalK3_informationLE hv F
  change (⟨F.evalK3Partial v⟩ : K3.Information) ≤ ⟨F.evalK3 (K3.ofBool ∘ t)⟩ at h
  rw [evalK3_total] at h
  have he := (K3.Information.le_iff_toOptionBool _ _).1 h b hb
  change (K3.ofOptionBool (some (F.eval t))).toOptionBool = some b at he
  rwa [K3.toOptionBool_ofOptionBool, Option.some.injEq] at he

theorem completes_reduct (f : A → B) {v : PartialValuation B} {t : TotalValuation B}
    (h : Completes v t) : Completes (reduct f v) (reduct f t) :=
  fun a b hb => h (f a) b hb

theorem completion_lifts_iff (f : A → B) (v : PartialValuation B) {s : TotalValuation A}
    (hs : Completes (reduct f v) s) :
    (∃ t, Completes v t ∧ reduct f t = s) ↔
      ∀ a a', f a = f a' → s a = s a' := by
  classical
  constructor
  · rintro ⟨t, _, rfl⟩ a a' h
    exact congrArg t h
  · intro h
    let t : TotalValuation B := fun b =>
      if preimage : ∃ a, f a = b then s (Classical.choose preimage) else (v b).getD false
    refine ⟨t, ?_, ?_⟩
    · intro b c hc
      unfold t
      split
      · rename_i preimage
        apply hs (Classical.choose preimage) c
        simpa only [reduct, Function.comp_apply, Classical.choose_spec preimage] using hc
      · simp [hc]
    · funext a
      have preimage : ∃ a', f a' = f a := ⟨a, rfl⟩
      change t (f a) = s a
      rw [show t (f a) = s (Classical.choose preimage) from dite_eq_left preimage]
      exact h _ a (Classical.choose_spec preimage)

theorem superEval_rename_of_coverage (f : A → B) (v : PartialValuation B)
    (covers : CompletionCovers f v) (F : Problem A) :
    (F.rename f).superEval v = F.superEval (reduct f v) := by
  have known (b : Bool) : (F.rename f).superEval v = some b ↔
      F.superEval (reduct f v) = some b := by
    simp only [superEval_eq_some, eval_rename]
    constructor
    · intro h s hs
      obtain ⟨t, ht, rfl⟩ := covers s hs
      exact h t ht
    · exact fun h t ht => h (reduct f t) (completes_reduct f ht)
  cases hl : (F.rename f).superEval v with
  | some b => exact ((known b).1 hl).symm
  | none =>
    cases hr : F.superEval (reduct f v) with
    | none => rfl
    | some b => nomatch hl.symm.trans ((known b).2 hr)

theorem superEval_rename_informationLE (f : A → B) (v : PartialValuation B) (F : Problem A) :
    (⟨F.superEvalK3 (reduct f v)⟩ : K3.Information) ≤ ⟨(F.rename f).superEvalK3 v⟩ := by
  apply (K3.Information.le_iff_toOptionBool _ _).2
  intro b hb
  apply (superEval_eq_some _ _ _).2
  intro t ht
  rw [eval_rename]
  exact (superEval_eq_some _ _ _).1 hb _ (completes_reduct f ht)

end Silmaril.Proofs.Logic.SAT.Institution
