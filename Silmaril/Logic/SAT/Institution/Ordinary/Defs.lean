module

public import Silmaril.Logic.SAT.Institution.Thms
public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-! # Ordinary SAT institutions obtained by observing valuation semantics -/

namespace Silmaril.Logic.SAT.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.ManyValued

universe u

/-- A predicate on an exactly reindexing CNF evaluation gives an ordinary institution
with discrete valuation categories. -/
def observationInstitution {V W : Type}
    (evaluate : {A : Type u} → (A → V) → Problem A → W) (observes : W → Prop)
    (hEval : ∀ {A B : Type u} (f : A → B) (v : B → V) (F : Problem A),
      evaluate v (F.rename f) = evaluate (reduct f v) F) : Type u ⥤ Room.{u, u, u} where
  obj A := ⟨Problem A, Cat.of (Discrete (A → V)), fun M F => observes (evaluate (Discrete.as M) F)⟩
  map f := ⟨Problem.rename f, Discrete.functor (fun v => Discrete.mk (reduct f v)),
    fun M F => iff_of_eq (congrArg observes (hEval f (Discrete.as M) F))⟩
  map_id _ := Room.hom_ext Problem.rename_id (Discrete.functor_ext fun _ => rfl)
  map_comp f g := Room.hom_ext (Problem.rename_comp f g) (Discrete.functor_ext fun _ => rfl)

/-- Total Boolean valuations and classical satisfaction of CNF problems. -/
def totalInstitution : Type u ⥤ Room.{u, u, u} :=
  observationInstitution Problem.eval (· = true) Problem.eval_rename

/-- Partial valuations observed by strong Kleene truth. -/
def kleeneTruthInstitution : Type u ⥤ Room.{u, u, u} :=
  observationInstitution Problem.evalK3Partial (· = K3.ofBool true) Problem.evalK3Partial_rename

/-- Partial valuations observed by strong Kleene falsity. -/
def kleeneRefutationInstitution : Type u ⥤ Room.{u, u, u} :=
  observationInstitution Problem.evalK3Partial (· = K3.ofBool false) Problem.evalK3Partial_rename

/-- Evidence valuations observed by positive support, including the value `both`. -/
def evidenceSupportInstitution : Type u ⥤ Room.{u, u, u} :=
  observationInstitution Problem.evalEvidence (fun e => e.support = true) Problem.evalEvidence_rename

/-- Evidence valuations observed by refutation, including the value `both`. -/
def evidenceRefutationInstitution : Type u ⥤ Room.{u, u, u} :=
  observationInstitution Problem.evalEvidence (fun e => e.refute = true) Problem.evalEvidence_rename

end Silmaril.Logic.SAT.Institution
