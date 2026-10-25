module

public import Silmaril.Calculi.LambdaCube.PTS
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

set_option autoImplicit true

/-! # Parameterized semantics for the polymorphic and dependent corners

This interface supplies no PER or realizability construction. A client must
provide its model category, satisfaction relation, and typing soundness.
In particular it does not extend the STLC full-function set model to System F.
-/

namespace Silmaril.Calculi.LambdaCube

open CategoryTheory Silmaril.Logic.Institution

/-- PTS judgments, including open typing and typed conversion assertions. -/
inductive PTSJudgment where
  | typing (Γ : List (Pseudo CubeSort)) (t A : Pseudo CubeSort)
  | equation (Γ : List (Pseudo CubeSort)) (t u A : Pseudo CubeSort)

/-- Derivability of the two sentence forms at a cube corner. -/
def PTSJudgment.Derivable (c : Corner) : PTSJudgment → Prop
  | .typing Γ t A => HasType c.specification Γ t A
  | .equation Γ t u A => HasType c.specification Γ t A ∧
      HasType c.specification Γ u A ∧ Pseudo.Conv t u

/-- All cube edges preserve judgment derivability; syntax translation is identity. -/
theorem PTSJudgment.inclusion {c d : Corner} (h : c ≤ d) {j : PTSJudgment}
    (hj : j.Derivable c) : j.Derivable d := by
  cases j with
  | typing Γ t A => exact Corner.typing_inclusion h hj
  | equation Γ t u A => exact ⟨Corner.typing_inclusion h hj.1,
      Corner.typing_inclusion h hj.2.1, hj.2.2⟩

/-- In particular STLC embeds into System F at the level of PTS judgments.
This is not yet a semantic comorphism from the concrete set institution. -/
theorem stlc_to_systemF {j : PTSJudgment} (h : j.Derivable Corner.stlc) :
    j.Derivable Corner.systemF := j.inclusion Corner.stlc_le_systemF h

/-- Reflection of PTS equations on the already STLC-typed fragment. -/
theorem PTSJudgment.systemF_equation_iff {Γ t u A}
    (ht : HasType Corner.stlc.specification Γ t A)
    (hu : HasType Corner.stlc.specification Γ u A) :
    (PTSJudgment.equation Γ t u A).Derivable Corner.systemF ↔
      (PTSJudgment.equation Γ t u A).Derivable Corner.stlc :=
  Corner.systemF_conservative ht hu

/-- The semantic boundary for F, Fω, or any other corner. No model existence
is inferred from this structure. Empty model categories remain possible. -/
structure Semantics (c : Corner) where
  Model : Type 1
  [category : Category.{1} Model]
  sat : Model → PTSJudgment → Prop
  sound : ∀ {j}, j.Derivable c → ∀ M, sat M j

attribute [instance] Semantics.category

/-- A single-signature room of PTS judgments with supplied semantics. -/
def Semantics.room {c : Corner} (M : Semantics c) : Room.{0, 1, 1} :=
  ⟨PTSJudgment, Cat.of M.Model, M.sat⟩

/-- The institution over one signature; extension with constants/signature
morphisms needs additional substitution and reduct data from the model provider. -/
def Semantics.institution {c : Corner} (M : Semantics c) : Discrete Unit ⥤ Room.{0, 1, 1} :=
  Discrete.functor (fun _ => M.room)

/-- The bundled single-signature institution. -/
def Semantics.inst {c : Corner} (M : Semantics c) : Inst.{0, 0, 0, 1, 1} :=
  ⟨Discrete Unit, M.institution⟩

/-- Required model data along a cube inclusion: functorial reducts and an
iff satisfaction law. Derivation preservation alone does not provide these. -/
structure SemanticInclusion {c d : Corner} (h : c ≤ d)
    (M : Semantics c) (N : Semantics d) where
  reduct : N.Model ⥤ M.Model
  satisfaction : ∀ X j, N.sat X j ↔ M.sat (reduct.obj X) j

/-- A semantic inclusion gives the corridor in the comorphism direction. -/
def SemanticInclusion.corridor {c d : Corner} {h : c ≤ d}
    {M : Semantics c} {N : Semantics d} (f : SemanticInclusion h M N) : M.room ⟶ N.room :=
  ⟨id, f.reduct, f.satisfaction⟩

/-- With actual model reducts, cube inclusions yield institution comorphisms. -/
def SemanticInclusion.comorphism {c d : Corner} {h : c ≤ d}
    {M : Semantics c} {N : Semantics d} (f : SemanticInclusion h M N) :
    Inst.CoHom M.inst N.inst where
  Φ := 𝟭 _
  ρ := Discrete.natTrans (fun _ => f.corridor)

/-- System F is the polymorphic PTS corner, with the semantic boundary explicit. -/
abbrev SystemFSemantics := Semantics Corner.systemF

/-- System Fω adds higher type constructors to System F. -/
abbrev SystemFOmegaSemantics := Semantics Corner.systemFOmega

end Silmaril.Calculi.LambdaCube
