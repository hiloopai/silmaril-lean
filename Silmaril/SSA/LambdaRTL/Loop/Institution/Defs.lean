module

public import Silmaril.SSA.LambdaRTL.Loop.Thms
public import Silmaril.SSA.LambdaRTL.Institution.Defs

/-!
# Equivalence/refinement-in-context institutions for λSSA and λRTL with loops

As `Silmaril.SSA.LambdaRTL.Institution` (acyclic stage), for the loop syntax `Loop.Region` over a
monad with a lawful Elgot iteration: `loopSSA R` (dominance-scoped SSA judgements, lexical
semantics), `loopRTLObs R` (arbitrary λRTL judgements, observational store semantics), and the
comorphism `loopSSAToRTL R` whose satisfaction condition is the agreement theorem with loops
`Loop.Region.evalObs_eq_evalSSA_of_isSSA`. `R` is any relation on outcomes (`Eq`:
equivalence-in-context; a preorder: refinement-in-context).
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.Loop.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Elgot
open Silmaril.SSA.LambdaRTL.Institution (Sig reductFunctor reductFunctor_id reductFunctor_comp)

variable (V L : Type) [DecidableEq V] [DecidableEq L] (M : Type → Type) [Monad M] [Iterate M]
  (α : Type)

/-- A judgement `Γ ⊢ r ⋈ r'` over the loop syntax. -/
structure Judgement (F : Type) where
  ctx : Finset V
  lhs : Region V L F
  rhs : Region V L F

/-- A λSSA judgement with loops: both sides dominance-scoped SSA in the context. -/
structure SSAJudgement (F : Type) extends Judgement V L F where
  lhs_ssa : lhs.IsSSA ctx
  rhs_ssa : rhs.IsSSA ctx

variable {V L}

omit [DecidableEq L] in
theorem SSAJudgement.ext' {F : Type} {j k : SSAJudgement V L F} (hc : j.ctx = k.ctx)
    (hl : j.lhs = k.lhs) (hr : j.rhs = k.rhs) : j = k := by
  rcases j with ⟨⟨_, _, _⟩, _, _⟩; rcases k with ⟨⟨_, _, _⟩, _, _⟩
  cases hc; cases hl; cases hr; rfl

/-- Renaming instructions in a judgement. -/
def Judgement.map {F F' : Type} (h : F → F') (j : Judgement V L F) : Judgement V L F' :=
  ⟨j.ctx, j.lhs.mapOp h, j.rhs.mapOp h⟩

/-- Renaming instructions in an SSA judgement. -/
def SSAJudgement.map {F F' : Type} (h : F → F') (j : SSAJudgement V L F) :
    SSAJudgement V L F' :=
  ⟨j.toJudgement.map h, (Region.isSSA_mapOp h _ _).2 j.lhs_ssa,
    (Region.isSSA_mapOp h _ _).2 j.rhs_ssa⟩

variable (V L)

/-- The room of λSSA judgements with loops over `F`. -/
def ssaRoom (R : M (L × α) → M (L × α) → Prop) (S : Sig) : Room.{0, 0, 0} where
  Sen := SSAJudgement V L S.ops
  Mod := Cat.of (Discrete (Model S.ops M α))
  Sat m j := ∀ ρ : V → α, R (j.lhs.evalSSA m.as ρ) (j.rhs.evalSSA m.as ρ)

/-- The λSSA-with-loops equivalence/refinement-in-context institution. -/
def loopSSA (R : M (L × α) → M (L × α) → Prop) : Inst.{1, 0, 0, 0, 0} where
  Sign := Sig
  I :=
    { obj := ssaRoom V L M α R
      map {S S'} h :=
        ⟨SSAJudgement.map h, reductFunctor h, fun m j => by
          change (∀ ρ, R ((j.lhs.mapOp h).evalSSA m.as ρ) ((j.rhs.mapOp h).evalSSA m.as ρ)) ↔
            ∀ ρ, R (j.lhs.evalSSA (m.as.reduct h) ρ) (j.rhs.evalSSA (m.as.reduct h) ρ)
          simp only [Region.evalSSA_mapOp]⟩
      map_id S := by
        apply Room.hom_ext
        · funext j
          change SSAJudgement.map id j = j
          cases j with | mk j _ _ => cases j with | mk Γ r r' =>
          simp only [SSAJudgement.map, Judgement.map, Region.mapOp_id]
        · exact reductFunctor_id S.ops
      map_comp {S S' S''} h k := by
        apply Room.hom_ext
        · funext j
          change SSAJudgement.map (k ∘ h) j = SSAJudgement.map k (SSAJudgement.map h j)
          cases j with | mk j _ _ => cases j with | mk Γ r r' =>
          simp only [SSAJudgement.map, Judgement.map, Region.mapOp_comp]
        · exact reductFunctor_comp h k }

/-- The room of λRTL judgements with loops over `F` (observational). -/
def rtlObsRoom (R : M (L × α) → M (L × α) → Prop) (S : Sig) : Room.{0, 0, 0} where
  Sen := Judgement V L S.ops
  Mod := Cat.of (Discrete (Model S.ops M α))
  Sat m j := ∀ σ : V → α, R (j.lhs.evalObs m.as σ) (j.rhs.evalObs m.as σ)

/-- The observational λRTL-with-loops equivalence/refinement-in-context institution. -/
def loopRTLObs (R : M (L × α) → M (L × α) → Prop) : Inst.{1, 0, 0, 0, 0} where
  Sign := Sig
  I :=
    { obj := rtlObsRoom V L M α R
      map {S S'} h :=
        ⟨Judgement.map h, reductFunctor h, fun m j => by
          change (∀ σ, R ((j.lhs.mapOp h).evalObs m.as σ) ((j.rhs.mapOp h).evalObs m.as σ)) ↔
            ∀ σ, R (j.lhs.evalObs (m.as.reduct h) σ) (j.rhs.evalObs (m.as.reduct h) σ)
          simp only [Region.evalObs_mapOp]⟩
      map_id S := by
        apply Room.hom_ext
        · funext j
          change Judgement.map id j = j
          cases j with | mk Γ r r' =>
          simp only [Judgement.map, Region.mapOp_id]
        · exact reductFunctor_id S.ops
      map_comp {S S' S''} h k := by
        apply Room.hom_ext
        · funext j
          change Judgement.map (k ∘ h) j = Judgement.map k (Judgement.map h j)
          cases j with | mk Γ r r' =>
          simp only [Judgement.map, Region.mapOp_comp]
        · exact reductFunctor_comp h k }

/-! ## Embedding the acyclic stage -/

/-- **Comorphism** acyclic λSSA → λSSA with loops (embedding `Region.ofAcyclic`); identity on
signatures and models. Needs only an iteration operator, no Elgot law. -/
def acyclicToLoopSSA (R : M (L × α) → M (L × α) → Prop) :
    Inst.CoHom (LambdaRTL.Institution.ssa V L M α R) (loopSSA V L M α R) where
  Φ := 𝟭 Sig
  ρ :=
    { app S := ⟨fun j => ⟨⟨j.ctx, Region.ofAcyclic j.lhs, Region.ofAcyclic j.rhs⟩,
          (Region.isSSA_ofAcyclic _ _).2 j.lhs_ssa, (Region.isSSA_ofAcyclic _ _).2 j.rhs_ssa⟩,
        𝟭 _, fun m j => by
          change (∀ ρ, R ((Region.ofAcyclic j.lhs).evalSSA m.as ρ)
              ((Region.ofAcyclic j.rhs).evalSSA m.as ρ)) ↔
            ∀ ρ, R (j.lhs.evalSSA m.as ρ) (j.rhs.evalSSA m.as ρ)
          simp only [Region.evalSSA_ofAcyclic]⟩
      naturality := by
        intro S S' h
        apply Room.hom_ext
        · funext j
          exact SSAJudgement.ext' rfl (Region.mapOp_ofAcyclic h _).symm
            (Region.mapOp_ofAcyclic h _).symm
        · exact CategoryTheory.Functor.ext (fun m => by cases m; rfl) }

variable [LawfulMonad M] [LawfulElgotMonad M]

/-- **Comorphism** λSSA → λRTL with loops; its satisfaction condition is the agreement theorem
with loops. -/
def loopSSAToRTL (R : M (L × α) → M (L × α) → Prop) :
    Inst.CoHom (loopSSA V L M α R) (loopRTLObs V L M α R) where
  Φ := 𝟭 Sig
  ρ :=
    { app S := ⟨SSAJudgement.toJudgement, 𝟭 _, fun m j => by
        change (∀ σ, R (j.lhs.evalObs m.as σ) (j.rhs.evalObs m.as σ)) ↔
          ∀ ρ, R (j.lhs.evalSSA m.as ρ) (j.rhs.evalSSA m.as ρ)
        simp only [Region.evalObs_eq_evalSSA_of_isSSA m.as j.lhs_ssa,
          Region.evalObs_eq_evalSSA_of_isSSA m.as j.rhs_ssa]⟩
      naturality := by
        intro S S' h
        apply Room.hom_ext
        · rfl
        · exact CategoryTheory.Functor.ext (fun m => by cases m; rfl) }

end Silmaril.SSA.LambdaRTL.Loop.Institution
