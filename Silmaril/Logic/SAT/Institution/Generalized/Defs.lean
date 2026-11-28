module

public import Silmaril.Logic.Institution.Generalized.Defs
public import Silmaril.Logic.SAT.Institution.Ordinary.Defs
import Silmaril.Logic.ManyValued.Thms

@[expose] public section

/-! # Generalized institutions of SAT valuation semantics -/

namespace Silmaril.Logic.SAT.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.ManyValued

universe u

/-- Total Boolean evaluation on the ordinary CNF sentence and valuation functors. -/
def totalExact : Generalized.ExactInstitution (Type u) Bool where
  Sen := sentenceFunctor totalInstitution
  Mod := modelFunctor totalInstitution
  eval _ M F := F.eval (Discrete.as M)
  eval_map f M F := Problem.eval_rename f (Discrete.as M) F

/-- Compositional strong Kleene evaluation on partial valuations. -/
def kleeneExact : Generalized.ExactInstitution (Type u) K3 where
  Sen := totalExact.Sen
  Mod := modelFunctor kleeneTruthInstitution
  eval _ M F := F.evalK3Partial (Discrete.as M)
  eval_map f M F := Problem.evalK3Partial_rename f (Discrete.as M) F

/-- Compositional FDE evaluation retains the Boolean support and refutation bits. -/
def evidenceExact : Generalized.ExactInstitution (Type u) FDE where
  Sen := totalExact.Sen
  Mod := modelFunctor evidenceSupportInstitution
  eval _ M F := F.evalEvidence (Discrete.as M)
  eval_map f M F := Problem.evalEvidence_rename f (Discrete.as M) F

/-- Read each finite evidence bit as a proposition. -/
def fdeToGeneralizedEvidence (e : FDE) : Generalized.Evidence :=
  ⟨e.support = true, e.refute = true⟩

theorem fdeToGeneralizedEvidence_mono {a b : FDE}
    (h : (⟨a⟩ : FDE.Information) ≤ ⟨b⟩) :
    fdeToGeneralizedEvidence a ≤ fdeToGeneralizedEvidence b :=
  let h := (FDE.Information.le_iff_bits ⟨a⟩ ⟨b⟩).1 h
  ⟨Bool.le_iff_imp.1 h.1, Bool.le_iff_imp.1 h.2⟩

/-- Completion evaluation is lax in the shared information order for all atom maps. -/
noncomputable def completionLax : Generalized.LaxInstitution (Type u) Generalized.Evidence where
  Sen := kleeneExact.Sen
  Mod := kleeneExact.Mod
  eval _ M F := fdeToGeneralizedEvidence (F.completionEvidence (Discrete.as M))
  le_eval_map f M F := fdeToGeneralizedEvidence_mono
    (Problem.completionEvidence_rename_informationLE f (Discrete.as M) F)

end Silmaril.Logic.SAT.Institution
