module

public import Silmaril.Logic.SAT.Institution.Generalized.Defs

@[expose] public section

namespace Silmaril.Logic.SAT.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.ManyValued

universe u
variable {A B : Type u}

theorem totalExact_truth_iff (v : TotalValuation A) (F : Problem A) :
    (totalExact.observe (· = true)).Sat A (Discrete.mk v) F ↔
      (totalInstitution.obj A).Sat (Discrete.mk v) F := Iff.rfl

theorem kleeneExact_truth_iff (v : PartialValuation A) (F : Problem A) :
    (kleeneExact.observe (· = K3.ofBool true)).Sat A (Discrete.mk v) F ↔
      (kleeneTruthInstitution.obj A).Sat (Discrete.mk v) F := Iff.rfl

theorem kleeneExact_refutation_iff (v : PartialValuation A) (F : Problem A) :
    (kleeneExact.observe (· = K3.ofBool false)).Sat A (Discrete.mk v) F ↔
      (kleeneRefutationInstitution.obj A).Sat (Discrete.mk v) F := Iff.rfl

theorem evidenceExact_support_iff (v : EvidenceValuation A) (F : Problem A) :
    (evidenceExact.observe (fun e => e.support = true)).Sat A (Discrete.mk v) F ↔
      (evidenceSupportInstitution.obj A).Sat (Discrete.mk v) F := Iff.rfl

theorem evidenceExact_refutation_iff (v : EvidenceValuation A) (F : Problem A) :
    (evidenceExact.observe (fun e => e.refute = true)).Sat A (Discrete.mk v) F ↔
      (evidenceRefutationInstitution.obj A).Sat (Discrete.mk v) F := Iff.rfl

/-- The exact institution projects to the legacy compositional verdict. -/
theorem kleeneExact_toOptionBool (v : PartialValuation A) (F : Problem A) :
    (kleeneExact.eval A (Discrete.mk v) F).toOptionBool = F.evalK3Option v := rfl

/-- The generalized flags are the two independent universal completion tests. -/
theorem completionLax_eval_eq_ofCompletions (v : PartialValuation A) (F : Problem A) :
    completionLax.eval A (Discrete.mk v) F =
      Generalized.Evidence.ofCompletions {t | Completes v t} (fun t => F.eval t = true) :=
  Generalized.Evidence.ext (propext (Problem.completionEvidence_support_iff v F))
    (propext ((Problem.completionEvidence_refute_iff v F).trans
      (forall_congr' fun _ => imp_congr_right fun _ => Bool.eq_false_iff)))

/-- The generalized flags also agree with the embedded typed supervaluation verdict. -/
theorem completionLax_eval_eq_ofSuperEvalK3 (v : PartialValuation A) (F : Problem A) :
    completionLax.eval A (Discrete.mk v) F = fdeToGeneralizedEvidence (F.superEvalK3 v).toFDE :=
  congrArg fdeToGeneralizedEvidence (Problem.completionEvidence_eq_ofK3_superEval v F)

/-- For a covering map both completion flags are exact, including for all injections. -/
theorem completionLax_eval_map_of_coverage (f : A → B) (v : PartialValuation B)
    (covers : CompletionCovers f v) (F : Problem A) :
    completionLax.eval B (Discrete.mk v) (F.rename f) =
      completionLax.eval A (Discrete.mk (reduct f v)) F :=
  congrArg fdeToGeneralizedEvidence (Problem.completionEvidence_rename_of_coverage f v covers F)

end Silmaril.Logic.SAT.Institution
