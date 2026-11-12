module

public import Silmaril.Raw.SSA.Isotope.Institution.Observational.Isomorphism

/-!
# Non-vacuity of the observational institutions

The observational institutions of `Silmaril.Isotope.Institution.Observational` are not
degenerate:

* every scope has a model (`unitModel`), with one-point value and state carriers, no
  instructions, no faults and no divergent primitives;
* some sentences fail: `unit ≐ inl unit` is not valid in let-iter (`letIter_not_obsEq`),
  let-case (`letCase_not_obsEq`), lambda-SSA (`lambdaSSA_not_obsEq`, transported along the
  `iterSSA` comorphism) or the quotient institutions (`letIterQ_not_obsEq`,
  `lambdaSSAQ_not_obsEq`), and `unit ⊑ inl unit` fails at `unitModel`;
* some non-reflexive equations hold in every model: the let-eta law `let x = a in x ≐ a`
  (`letIter_obsEq_letEta`, from `LetIter.LocallyNameless.obs_letEta`), also after compilation to
  lambda-SSA (`lambdaSSA_obsEq_compile_letEta`);
* the isomorphism `iterSSAIso` relates quotient institutions with distinct sentences
  (`letIterQ_unit_ne_inl`).
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Institution.Observational

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Observational
open Silmaril.Isotope.Morphism.SSAIter (termSetoid regionSetoid compileSingle compileSingle_scoped)

variable {Φ : Type u}

/-- The let-iter program `unit`. -/
abbrev iUnit (Φ : Type u) (n : Nat) : LetIter.LocallyNameless.Tm Empty Φ n := .unit

/-- The let-iter program `inl unit`. -/
abbrev iInl (Φ : Type u) (n : Nat) : LetIter.LocallyNameless.Tm Empty Φ n := .inl .unit

/-- A model at every scope: one-point carriers, no instructions, no faults, no divergent
primitives, all bound variables `unit`. -/
def unitModel (Φ : Type u) (n : Nat) : Model.{u, v, w} Φ n where
  α := PUnit
  σ := PUnit
  instr _ _ _ _ _ := False
  faults _ _ _ _ := False
  prim _ _ _ := False
  bound _ := .unit

/-- Every scope has a model, so no model category is empty. -/
instance (n : Nat) : Nonempty (Model.{u, v, w} Φ n) := ⟨unitModel Φ n⟩

/-- The program `unit` returns `unit` at `unitModel`. -/
theorem unit_mem_iterBeh (n : Nat) :
    Observation.ret PUnit.unit Value.unit PUnit.unit ∈
      iterBeh (unitModel.{u, v, w} Φ n) (iUnit Φ n) :=
  LetIter.Semantics.Eval.unit

/-- The program `inl unit` never returns `unit`. -/
theorem unit_not_mem_iterBeh_inl (n : Nat) :
    Observation.ret PUnit.unit Value.unit PUnit.unit ∉
      iterBeh (unitModel.{u, v, w} Φ n)
        (iInl Φ n) := by
  intro h
  have h' : LetIter.Semantics.Eval (unitModel.{u, v, w} Φ n).instr noFree
      (unitModel.{u, v, w} Φ n).bound (iInl Φ n) PUnit.unit Value.unit PUnit.unit := h
  cases h'

/-- The refinement `unit ⊑ inl unit` fails at `unitModel`. -/
theorem letIter_not_sat_le (n : Nat) :
    ¬ ((letIter.{u, v, w} Φ).room n).Sat (Discrete.mk (unitModel.{u, v, w} Φ n))
      (.le (iUnit Φ n) (iInl Φ n)) :=
  fun h => unit_not_mem_iterBeh_inl n (h (unit_mem_iterBeh n))

/-- The equation `unit ≐ inl unit` is not valid in let-iter. -/
theorem letIter_not_obsEq (n : Nat) :
    ¬ (letIter.{u, v, w} Φ).ObsEq (iUnit Φ n) (iInl Φ n) := by
  intro h
  have e : iterBeh (unitModel.{u, v, w} Φ n) (iUnit Φ n) =
      iterBeh (unitModel.{u, v, w} Φ n) (iInl Φ n) :=
    ((letIter.{u, v, w} Φ).obsEq_iff _ _).mp h (unitModel Φ n)
  exact unit_not_mem_iterBeh_inl n (e ▸ unit_mem_iterBeh n)

/-- The equation `unit ≐ inl unit` is not valid in let-case, via the `caseIter` comorphism. -/
theorem letCase_not_obsEq (n : Nat) :
    ¬ (letCase.{u, v, w} Φ).ObsEq
      (LetCase.LocallyNameless.Tm.unit : LetCase.LocallyNameless.Tm Empty Φ n)
      (LetCase.LocallyNameless.Tm.inl .unit : LetCase.LocallyNameless.Tm Empty Φ n) :=
  fun h => letIter_not_obsEq.{u, v, w} n (((caseIter.{u, v, w} Φ).obsEq_iff _ _).mpr h)

/-- The compiled equation `unit ≐ inl unit` is not valid in lambda-SSA, via the `iterSSA`
comorphism. -/
theorem lambdaSSA_not_obsEq (n : Nat) :
    ¬ (lambdaSSA.{u, v, w} Φ 1).ObsEq ((iterSSA.{u, v, w} Φ).prog (iUnit Φ n))
      ((iterSSA.{u, v, w} Φ).prog (iInl Φ n)) :=
  fun h => letIter_not_obsEq.{u, v, w} n (((iterSSA.{u, v, w} Φ).obsEq_iff _ _).mp h)

/-- The let-eta law `let x = a in x ≐ a` is valid in let-iter, from
`LetIter.LocallyNameless.obs_letEta`. -/
theorem letIter_obsEq_letEta {n : Nat} (a : LetIter.LocallyNameless.Tm Empty Φ n) :
    (letIter.{u, v, w} Φ).ObsEq (LetIter.LocallyNameless.Tm.let₁ a (.bv 0)) a :=
  (iter_obs_iff _ _).mp (LetIter.LocallyNameless.obs_letEta a)

/-- The let-eta law survives compilation to lambda-SSA, via the `iterSSA` comorphism. -/
theorem lambdaSSA_obsEq_compile_letEta {n : Nat} (a : LetIter.LocallyNameless.Tm Empty Φ n) :
    (lambdaSSA.{u, v, w} Φ 1).ObsEq
      ((iterSSA.{u, v, w} Φ).prog (LetIter.LocallyNameless.Tm.let₁ a (.bv 0)))
      ((iterSSA.{u, v, w} Φ).prog a) :=
  ((iterSSA.{u, v, w} Φ).obsEq_iff _ _).mpr (letIter_obsEq_letEta a)

/-- The equation `⟦unit⟧ ≐ ⟦inl unit⟧` is not valid in the quotient let-iter institution. -/
theorem letIterQ_not_obsEq (n : Nat) :
    ¬ (letIterQ.{u, v, w} Φ).ObsEq (n := n)
      (Quotient.mk (termSetoid.{u, v, w} Φ n) (iUnit Φ n))
      (Quotient.mk (termSetoid.{u, v, w} Φ n) (iInl Φ n)) := by
  intro h
  exact letIter_not_obsEq.{u, v, w} n (((letIter.{u, v, w} Φ).obsEq_iff _ _).mpr
    (((letIterQ.{u, v, w} Φ).obsEq_iff _ _).mp h))

/-- The quotient let-iter institution has distinct programs. -/
theorem letIterQ_unit_ne_inl (n : Nat) :
    Quotient.mk (termSetoid.{u, v, w} Φ n) (iUnit Φ n) ≠
      Quotient.mk (termSetoid.{u, v, w} Φ n) (iInl Φ n) := by
  intro h
  apply letIterQ_not_obsEq.{u, v, w} (Φ := Φ) n
  rw [h]
  exact ((letIterQ.{u, v, w} Φ).obsEq_iff _ _).mpr fun _ => rfl

/-- The image of `⟦unit⟧ ≐ ⟦inl unit⟧` under the isomorphism `iterSSAIso` is not valid in the
quotient lambda-SSA institution. -/
theorem lambdaSSAQ_not_obsEq (n : Nat) :
    ¬ (lambdaSSAQ.{u, v, w} Φ).ObsEq ((compileQ.{u, v, w} Φ).prog (n := n)
        (Quotient.mk (termSetoid.{u, v, w} Φ n) (iUnit Φ n)))
      ((compileQ.{u, v, w} Φ).prog (Quotient.mk (termSetoid.{u, v, w} Φ n) (iInl Φ n))) :=
  fun h => letIterQ_not_obsEq.{u, v, w} n (((compileQ.{u, v, w} Φ).obsEq_iff _ _).mp h)

end Silmaril.Isotope.Institution.Observational
