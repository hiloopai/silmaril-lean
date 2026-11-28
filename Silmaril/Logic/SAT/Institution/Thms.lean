module

public import Silmaril.Logic.SAT.Institution.Defs
import Silmaril.Logic.ManyValued.Thms
import Silmaril.Proofs.Logic.SAT.Institution.Evaluation
import Silmaril.Proofs.Logic.SAT.Institution.Completion

@[expose] public section

/-! # Change of signature and completion coverage for SAT valuations -/

namespace Silmaril.Logic.SAT.Institution

open Silmaril.Logic.ManyValued

universe u v w
variable {A : Type u} {B : Type v}

theorem toOptionBool_eq_some_iff (k : K3) (b : Bool) :
    k.toOptionBool = some b ↔ k = K3.ofBool b :=
  Proofs.Logic.SAT.Institution.toOptionBool_eq_some_iff k b

namespace Problem

theorem rename_id : rename (id : A → A) = id := Proofs.Logic.SAT.Institution.rename_id

theorem rename_comp {D : Type w} (f : A → B) (g : B → D) :
    rename (g ∘ f) = rename g ∘ rename f := Proofs.Logic.SAT.Institution.rename_comp f g

theorem eval_rename (f : A → B) (v : TotalValuation B) (F : Problem A) :
    (F.rename f).eval v = F.eval (reduct f v) := Proofs.Logic.SAT.Institution.eval_rename f v F

theorem evalK3_rename (f : A → B) (v : K3Valuation B) (F : Problem A) :
    (F.rename f).evalK3 v = F.evalK3 (reduct f v) :=
  Proofs.Logic.SAT.Institution.evalWith_rename _ _ _ _ _ f v F

theorem evalK3Partial_rename (f : A → B) (v : PartialValuation B) (F : Problem A) :
    (F.rename f).evalK3Partial v = F.evalK3Partial (reduct f v) :=
  evalK3_rename f v.toK3 F

theorem evalK3Option_rename (f : A → B) (v : PartialValuation B) (F : Problem A) :
    (F.rename f).evalK3Option v = F.evalK3Option (reduct f v) :=
  congrArg K3.toOptionBool (evalK3Partial_rename f v F)

/-- The compatibility adapter computes the historical `Option Bool` fold. -/
theorem evalK3Option_eq_evalWith (v : PartialValuation A) (F : Problem A) :
    F.evalK3Option v =
      F.evalWith (some true) (some false) (Option.map Bool.not)
        (fun a b => if a = some false ∨ b = some false then some false
          else if a = some true ∧ b = some true then some true else none)
        (fun a b => if a = some true ∨ b = some true then some true
          else if a = some false ∧ b = some false then some false else none) v :=
  Proofs.Logic.SAT.Institution.evalK3Option_eq_evalWith v F

theorem evalEvidence_rename (f : A → B) (v : EvidenceValuation B) (F : Problem A) :
    (F.rename f).evalEvidence v = F.evalEvidence (reduct f v) :=
  Proofs.Logic.SAT.Institution.evalWith_rename _ _ _ _ _ f v F

/-- The translation preserves the existing Boolean evaluator at every assignment. -/
theorem eval_ofCNF (v : TotalValuation Nat) (F : SAT.CNF) :
    (ofCNF F).eval v = SAT.CNF.eval v F := Proofs.Logic.SAT.Institution.eval_ofCNF v F

theorem evalK3_total (v : TotalValuation A) (F : Problem A) :
    F.evalK3 (K3.ofBool ∘ v) = K3.ofBool (F.eval v) := Proofs.Logic.SAT.Institution.evalK3_total v F

theorem evalK3Option_total (v : TotalValuation A) (F : Problem A) :
    F.evalK3Option (some ∘ v) = some (F.eval v) := by
  change (F.evalK3 (K3.ofBool ∘ v)).toOptionBool = _
  rw [evalK3_total]
  exact K3.toOptionBool_ofOptionBool (some (F.eval v))

/-- Projection to the old evidence coordinates commutes with CNF evaluation. -/
theorem evalEvidence_bits (v : EvidenceValuation A) (F : Problem A) :
    ((F.evalEvidence v).support, (F.evalEvidence v).refute) =
      F.evalWith (true, false) (false, true) Prod.swap
        (fun a b => (a.1 && b.1, a.2 || b.2))
        (fun a b => (a.1 || b.1, a.2 && b.2))
        (fun a => ((v a).support, (v a).refute)) :=
  Proofs.Logic.SAT.Institution.evalEvidence_bits v F

theorem evalEvidence_ofK3 (v : K3Valuation A) (F : Problem A) :
    F.evalEvidence (K3.toFDE ∘ v) = (F.evalK3 v).toFDE :=
  Proofs.Logic.SAT.Institution.evalEvidence_ofK3 v F

theorem evalEvidence_total (v : TotalValuation A) (F : Problem A) :
    F.evalEvidence (K3.toFDE ∘ K3.ofBool ∘ v) = (K3.ofBool (F.eval v)).toFDE := by
  rw [evalEvidence_ofK3, evalK3_total]

theorem evalK3_informationLE {v v' : K3Valuation A}
    (h : ∀ a, (⟨v a⟩ : K3.Information) ≤ ⟨v' a⟩) (F : Problem A) :
    (⟨F.evalK3 v⟩ : K3.Information) ≤ ⟨F.evalK3 v'⟩ :=
  Proofs.Logic.SAT.Institution.evalK3_informationLE h F

theorem evalEvidence_informationLE {v v' : EvidenceValuation A}
    (h : ∀ a, (⟨v a⟩ : FDE.Information) ≤ ⟨v' a⟩) (F : Problem A) :
    (⟨F.evalEvidence v⟩ : FDE.Information) ≤ ⟨F.evalEvidence v'⟩ :=
  Proofs.Logic.SAT.Institution.evalEvidence_informationLE h F

end Problem

theorem exists_completion (v : PartialValuation A) : ∃ t, Completes v t :=
  Proofs.Logic.SAT.Institution.exists_completion v

theorem completes_reduct (f : A → B) {v : PartialValuation B} {t : TotalValuation B}
    (h : Completes v t) : Completes (reduct f v) (reduct f t) :=
  Proofs.Logic.SAT.Institution.completes_reduct f h

/-- A completion of the reduct lifts exactly when it is constant on the fibres of `f`. -/
theorem completion_lifts_iff (f : A → B) (v : PartialValuation B) {s : TotalValuation A}
    (hs : Completes (reduct f v) s) :
    (∃ t, Completes v t ∧ reduct f t = s) ↔ ∀ a a', f a = f a' → s a = s a' :=
  Proofs.Logic.SAT.Institution.completion_lifts_iff f v hs

theorem completionCovers_of_injective (f : A → B) (hf : Function.Injective f)
    (v : PartialValuation B) : CompletionCovers f v :=
  fun s hs => (completion_lifts_iff f v hs).2 fun _ _ h => congrArg s (hf h)

namespace Problem

theorem completionEvidence_support_iff (v : PartialValuation A) (F : Problem A) :
    (F.completionEvidence v).support = true ↔ ∀ t, Completes v t → F.eval t = true :=
  Proofs.Logic.SAT.Institution.completionEvidence_support_iff v F

theorem completionEvidence_refute_iff (v : PartialValuation A) (F : Problem A) :
    (F.completionEvidence v).refute = true ↔ ∀ t, Completes v t → F.eval t = false :=
  Proofs.Logic.SAT.Institution.completionEvidence_refute_iff v F

theorem completionEvidence_consistent (v : PartialValuation A) (F : Problem A) :
    ¬ ((F.completionEvidence v).support = true ∧ (F.completionEvidence v).refute = true) :=
  Proofs.Logic.SAT.Institution.completionEvidence_consistent v F

theorem completionEvidence_eq_ofK3_superEval (v : PartialValuation A) (F : Problem A) :
    F.completionEvidence v = (F.superEvalK3 v).toFDE :=
  Proofs.Logic.SAT.Institution.completionEvidence_eq_ofK3_superEval v F

theorem superEval_eq_some (v : PartialValuation A) (F : Problem A) (b : Bool) :
    F.superEval v = some b ↔ ∀ t, Completes v t → F.eval t = b :=
  Proofs.Logic.SAT.Institution.superEval_eq_some v F b

theorem superEval_eq_none (v : PartialValuation A) (F : Problem A) :
    F.superEval v = none ↔
      (∃ t, Completes v t ∧ F.eval t = true) ∧ (∃ t, Completes v t ∧ F.eval t = false) :=
  Proofs.Logic.SAT.Institution.superEval_eq_none v F

theorem superEval_total (t : TotalValuation A) (F : Problem A) :
    F.superEval (some ∘ t) = some (F.eval t) := Proofs.Logic.SAT.Institution.superEval_total t F

/-- Every compositional strong Kleene verdict survives quantification over total completions. -/
theorem evalK3_informationLE_superEval (v : PartialValuation A) (F : Problem A) :
    (⟨F.evalK3Partial v⟩ : K3.Information) ≤ ⟨F.superEvalK3 v⟩ :=
  Proofs.Logic.SAT.Institution.evalK3_informationLE_superEval v F

theorem superEval_rename_of_coverage (f : A → B) (v : PartialValuation B)
    (covers : CompletionCovers f v) (F : Problem A) :
    (F.rename f).superEval v = F.superEval (reduct f v) :=
  Proofs.Logic.SAT.Institution.superEval_rename_of_coverage f v covers F

theorem superEval_rename_of_injective (f : A → B) (hf : Function.Injective f)
    (v : PartialValuation B) (F : Problem A) :
    (F.rename f).superEval v = F.superEval (reduct f v) :=
  superEval_rename_of_coverage f v (completionCovers_of_injective f hf v) F

theorem superEvalK3_rename_of_coverage (f : A → B) (v : PartialValuation B)
    (covers : CompletionCovers f v) (F : Problem A) :
    (F.rename f).superEvalK3 v = F.superEvalK3 (reduct f v) :=
  by simpa only [Problem.superEval, K3.ofOptionBool_toOptionBool] using
    congrArg K3.ofOptionBool (superEval_rename_of_coverage f v covers F)

theorem superEvalK3_total (t : TotalValuation A) (F : Problem A) :
    F.superEvalK3 (some ∘ t) = K3.ofBool (F.eval t) :=
  (toOptionBool_eq_some_iff _ _).1 (superEval_total t F)

/-- Identification of atoms can remove completions and make an unknown verdict definite. -/
theorem superEval_rename_informationLE (f : A → B) (v : PartialValuation B) (F : Problem A) :
    (⟨F.superEvalK3 (reduct f v)⟩ : K3.Information) ≤ ⟨(F.rename f).superEvalK3 v⟩ :=
  Proofs.Logic.SAT.Institution.superEval_rename_informationLE f v F

/-- Covers preserve both universal flags exactly. -/
theorem completionEvidence_rename_of_coverage (f : A → B) (v : PartialValuation B)
    (covers : CompletionCovers f v) (F : Problem A) :
    (F.rename f).completionEvidence v = F.completionEvidence (reduct f v) := by
  simp only [completionEvidence_eq_ofK3_superEval, superEvalK3_rename_of_coverage f v covers]

/-- Every atom map preserves established universal flags from reduct to translation. -/
theorem completionEvidence_rename_informationLE (f : A → B) (v : PartialValuation B)
    (F : Problem A) :
    (⟨F.completionEvidence (reduct f v)⟩ : FDE.Information) ≤ ⟨(F.rename f).completionEvidence v⟩ := by
  simpa only [completionEvidence_eq_ofK3_superEval, K3.Information.toFDE] using
    (K3.Information.toFDE_le_iff _ _).2 (superEval_rename_informationLE f v F)

end Problem

end Silmaril.Logic.SAT.Institution
