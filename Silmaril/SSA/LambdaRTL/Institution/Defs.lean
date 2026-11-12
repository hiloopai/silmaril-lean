module

public import Silmaril.SSA.LambdaRTL.Thms
public import Silmaril.Logic.Institution.Morphism
public import Silmaril.Logic.Institution.Hets.LogicGraph
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Equivalence- and refinement-in-context institutions for acyclic λSSA and λRTL

Signatures are instruction alphabets (`Sig`, with renamings as morphisms). For a fixed monad
`M`, value carrier `α`, variable type `V`, label type `L` and a relation
`R : M (L × α) → M (L × α) → Prop` on observable outcomes:

* `ssa R` — sentences are **λSSA judgements in context** `Γ ⊢ r ⋈ r'` with `r`, `r'`
  dominance-scoped SSA in `Γ` (`Region.IsSSA`); a model satisfies the sentence when
  `R (⟦r⟧ρ) (⟦r'⟧ρ)` for every environment `ρ` under the lexical semantics.
* `rtlObs R` — sentences are arbitrary λRTL judgements `Γ ⊢ r ⋈ r'`; satisfaction compares the
  observable store semantics (final store dead).
* `rtlFull R'` — as `rtlObs`, but `R'` relates full outcomes, including the final store.

`R = Eq` gives equivalence-in-context; a preorder (e.g. an order on `M`) gives
refinement-in-context. Models form the *discrete* category on `Model F M α` at this stage;
model morphisms (value homomorphisms, Freyd/Elgot functors) are later stages
(`docs/projects/ssa.md`).

`ssaToRTL R : Inst.CoHom (ssa R) (rtlObs R)` is the comorphism that reads an SSA judgement as an
RTL judgement (identity on signatures and models). Its satisfaction condition is the agreement
theorem `Region.evalObs_eq_evalSSA_of_isSSA`; there is no comorphism on *all* λRTL sentences in
the other direction by the identity, by `Counterexample.clobber_counterexample`.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.Institution

open CategoryTheory Silmaril.Logic.Institution

/-- Instruction alphabets. -/
structure Sig : Type 1 where
  ops : Type

instance : Category Sig where
  Hom A B := A.ops → B.ops
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable (V L : Type) [DecidableEq V] [DecidableEq L] (M : Type → Type) [Monad M] (α : Type)

/-- A judgement in context `Γ ⊢ r ⋈ r'` (the relation `⋈` is fixed by the institution). -/
structure Judgement (F : Type) where
  ctx : Finset V
  lhs : Region V L F
  rhs : Region V L F

/-- A λSSA judgement: both sides are dominance-scoped SSA in the context. -/
structure SSAJudgement (F : Type) extends Judgement V L F where
  lhs_ssa : lhs.IsSSA ctx
  rhs_ssa : rhs.IsSSA ctx

variable {V L}

/-- Renaming instructions in a judgement. -/
def Judgement.map {F F' : Type} (h : F → F') (j : Judgement V L F) : Judgement V L F' :=
  ⟨j.ctx, j.lhs.mapOp h, j.rhs.mapOp h⟩

/-- Renaming instructions in an SSA judgement. -/
def SSAJudgement.map {F F' : Type} (h : F → F') (j : SSAJudgement V L F) :
    SSAJudgement V L F' :=
  ⟨j.toJudgement.map h, (Region.isSSA_mapOp h _ _).2 j.lhs_ssa,
    (Region.isSSA_mapOp h _ _).2 j.rhs_ssa⟩

variable {M α}

/-- Model reducts along a renaming, as a functor of discrete model categories. -/
def reductFunctor {F F' : Type} (h : F → F') :
    Discrete (Model F' M α) ⥤ Discrete (Model F M α) :=
  Discrete.functor fun m => Discrete.mk (m.reduct h)

omit [Monad M] in
theorem reductFunctor_id (F : Type) :
    reductFunctor (M := M) (α := α) (id : F → F) = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun m => by cases m; rfl)

omit [Monad M] in
theorem reductFunctor_comp {F F' F'' : Type} (h : F → F') (k : F' → F'') :
    reductFunctor (M := M) (α := α) (k ∘ h) = reductFunctor k ⋙ reductFunctor h :=
  CategoryTheory.Functor.ext (fun m => by cases m; rfl)

variable (V L M α)

/-! ## λSSA -/

/-- The room of λSSA judgements over `F`, satisfied lexically up to `R`. -/
def ssaRoom (R : M (L × α) → M (L × α) → Prop) (S : Sig) : Room.{0, 0, 0} where
  Sen := SSAJudgement V L S.ops
  Mod := Cat.of (Discrete (Model S.ops M α))
  Sat m j := ∀ ρ : V → α, R (j.lhs.evalSSA m.as ρ) (j.rhs.evalSSA m.as ρ)

/-- The λSSA equivalence/refinement-in-context institution. -/
def ssa (R : M (L × α) → M (L × α) → Prop) : Inst.{1, 0, 0, 0, 0} where
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

/-! ## λRTL -/

/-- The room of λRTL judgements over `F`, satisfied observationally up to `R`. -/
def rtlObsRoom (R : M (L × α) → M (L × α) → Prop) (S : Sig) : Room.{0, 0, 0} where
  Sen := Judgement V L S.ops
  Mod := Cat.of (Discrete (Model S.ops M α))
  Sat m j := ∀ σ : V → α, R (j.lhs.evalObs m.as σ) (j.rhs.evalObs m.as σ)

/-- The observational λRTL equivalence/refinement-in-context institution. -/
def rtlObs (R : M (L × α) → M (L × α) → Prop) : Inst.{1, 0, 0, 0, 0} where
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

/-- The room of λRTL judgements over `F`, satisfied on full outcomes (with final store). -/
def rtlFullRoom (R : M (L × α × (V → α)) → M (L × α × (V → α)) → Prop) (S : Sig) :
    Room.{0, 0, 0} where
  Sen := Judgement V L S.ops
  Mod := Cat.of (Discrete (Model S.ops M α))
  Sat m j := ∀ σ : V → α, R (j.lhs.evalRTL m.as σ) (j.rhs.evalRTL m.as σ)

/-- The full-store λRTL equivalence/refinement-in-context institution. -/
def rtlFull (R : M (L × α × (V → α)) → M (L × α × (V → α)) → Prop) : Inst.{1, 0, 0, 0, 0} where
  Sign := Sig
  I :=
    { obj := rtlFullRoom V L M α R
      map {S S'} h :=
        ⟨Judgement.map h, reductFunctor h, fun m j => by
          change (∀ σ, R ((j.lhs.mapOp h).evalRTL m.as σ) ((j.rhs.mapOp h).evalRTL m.as σ)) ↔
            ∀ σ, R (j.lhs.evalRTL (m.as.reduct h) σ) (j.rhs.evalRTL (m.as.reduct h) σ)
          simp only [Region.evalRTL_mapOp]⟩
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

/-! ## The comorphism λSSA → λRTL -/

variable [LawfulMonad M]

/-- The corridor at one signature: forget the SSA side conditions; models unchanged. -/
def ssaToRTLCorridor (R : M (L × α) → M (L × α) → Prop) (S : Sig) :
    ssaRoom V L M α R S ⟶ rtlObsRoom V L M α R S :=
  ⟨SSAJudgement.toJudgement, 𝟭 _, fun m j => by
    change (∀ σ, R (j.lhs.evalObs m.as σ) (j.rhs.evalObs m.as σ)) ↔
      ∀ ρ, R (j.lhs.evalSSA m.as ρ) (j.rhs.evalSSA m.as ρ)
    simp only [Region.evalObs_eq_evalSSA_of_isSSA m.as j.lhs_ssa,
      Region.evalObs_eq_evalSSA_of_isSSA m.as j.rhs_ssa]⟩

/-- **Comorphism** `λSSA → λRTL` (observational): reading an SSA judgement as a λRTL
judgement preserves and reflects satisfaction in every model. -/
def ssaToRTL (R : M (L × α) → M (L × α) → Prop) : Inst.CoHom (ssa V L M α R) (rtlObs V L M α R) where
  Φ := 𝟭 Sig
  ρ :=
    { app := ssaToRTLCorridor V L M α R
      naturality := by
        intro S S' h
        apply Room.hom_ext
        · rfl
        · exact CategoryTheory.Functor.ext (fun m => by cases m; rfl) }

/-! ## The Hets logic graph of this stage -/

/-- Logics of the acyclic stage. -/
inductive Logic
  | ssa
  | rtlObs
  deriving DecidableEq

/-- Comorphism edges of the acyclic stage. -/
inductive Edge : Logic → Logic → Type
  | ssaToRTL : Edge .ssa .rtlObs

/-- The institution of each logic, for a fixed outcome relation `R`. -/
def logicInst (R : M (L × α) → M (L × α) → Prop) : Logic → Inst.{1, 0, 0, 0, 0}
  | .ssa => ssa V L M α R
  | .rtlObs => rtlObs V L M α R

/-- The Hets logic graph `λSSA → λRTL(obs)`; no institution morphisms at this stage. -/
def hets (R : M (L × α) → M (L × α) → Prop) : LogicGraph.{0, 0, 1, 0, 0, 0, 0} where
  Logics := Logic
  inst := logicInst V L M α R
  Comor := Edge
  comor e := match e with
    | .ssaToRTL => ssaToRTL V L M α R
  Mor _ _ := PEmpty
  mor e := e.elim

end Silmaril.SSA.LambdaRTL.Institution
