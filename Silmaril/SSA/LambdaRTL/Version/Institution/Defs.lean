module

public import Silmaril.SSA.LambdaRTL.Version.Thms
public import Silmaril.SSA.LambdaRTL.Institution.Defs

/-!
# The versioning comorphism λRTL → λSSA (acyclic, pair-lawful models)

Versioning is only sound for models in which `unpair (pair a b) = pure (a, b)`
(`Model.PairLawful`), so this module adds the **pair-lawful** variants of the rooms of
`LambdaRTL.Institution`: same signatures (`Sig`), same sentences and satisfaction, but models
restricted to pair-lawful ones (`LawfulModel`). Reducts along instruction renamings preserve
pair-lawfulness. The existing institutions over all models are unchanged.

`versionCoHom R : Inst.CoHom (rtlObsL V L M α R) (ssaL (V × ℕ) L M α R)` maps a λRTL judgement
`Γ ⊢ r ⋈ r'` to the λSSA judgement `initCtx r ∪ initCtx r' ⊢ versionTop r ⋈ versionTop r'`
(the source context `Γ` is not used: λRTL stores are total), and is the identity on models and
signatures. Its satisfaction condition is `versionTop_evalSSA`, for any relation `R`.

Composing with `ssaToRTL` (restricted to lawful models) gives a λRTL → λRTL comorphism; that
it is the identity up to α-equivalence on SSA inputs is **not** claimed.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.SSA.LambdaRTL.Version

variable (V L : Type) [DecidableEq V] [DecidableEq L] (M : Type → Type) [Monad M] (α : Type)

/-- Pair-lawful models. -/
def LawfulModel (F : Type) : Type := {m : Model F M α // m.PairLawful}

variable {V L M α}

/-- Reducts preserve pair-lawfulness. -/
def LawfulModel.reduct {F F' : Type} (h : F → F') (m : LawfulModel M α F') : LawfulModel M α F :=
  ⟨m.1.reduct h, ⟨m.2.unpair_pair⟩⟩

/-- Reducts of pair-lawful models, as a functor of discrete categories. -/
def lawfulReductFunctor {F F' : Type} (h : F → F') :
    Discrete (LawfulModel M α F') ⥤ Discrete (LawfulModel M α F) :=
  Discrete.functor fun m => Discrete.mk (m.reduct h)

theorem lawfulReductFunctor_id (F : Type) :
    lawfulReductFunctor (M := M) (α := α) (id : F → F) = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun m => by cases m; rfl)

theorem lawfulReductFunctor_comp {F F' F'' : Type} (h : F → F') (k : F' → F'') :
    lawfulReductFunctor (M := M) (α := α) (k ∘ h) = lawfulReductFunctor k ⋙ lawfulReductFunctor h :=
  CategoryTheory.Functor.ext (fun m => by cases m; rfl)

variable (V L M α)

/-- λSSA judgements over pair-lawful models. -/
def ssaLRoom (R : M (L × α) → M (L × α) → Prop) (S : Sig) : Room.{0, 0, 0} where
  Sen := SSAJudgement V L S.ops
  Mod := Cat.of (Discrete (LawfulModel M α S.ops))
  Sat m j := ∀ ρ : V → α, R (j.lhs.evalSSA m.as.1 ρ) (j.rhs.evalSSA m.as.1 ρ)

/-- The λSSA institution over pair-lawful models. -/
def ssaL (R : M (L × α) → M (L × α) → Prop) : Inst.{1, 0, 0, 0, 0} where
  Sign := Sig
  I :=
    { obj := ssaLRoom V L M α R
      map {S S'} h :=
        ⟨SSAJudgement.map h, lawfulReductFunctor h, fun m j => by
          change (∀ ρ, R ((j.lhs.mapOp h).evalSSA m.as.1 ρ) ((j.rhs.mapOp h).evalSSA m.as.1 ρ)) ↔
            ∀ ρ, R (j.lhs.evalSSA (m.as.1.reduct h) ρ) (j.rhs.evalSSA (m.as.1.reduct h) ρ)
          simp only [Region.evalSSA_mapOp]⟩
      map_id S := by
        apply Room.hom_ext
        · funext j
          change SSAJudgement.map id j = j
          cases j with | mk j _ _ => cases j with | mk Γ r r' =>
          simp only [SSAJudgement.map, Judgement.map, Region.mapOp_id]
        · exact lawfulReductFunctor_id S.ops
      map_comp {S S' S''} h k := by
        apply Room.hom_ext
        · funext j
          change SSAJudgement.map (k ∘ h) j = SSAJudgement.map k (SSAJudgement.map h j)
          cases j with | mk j _ _ => cases j with | mk Γ r r' =>
          simp only [SSAJudgement.map, Judgement.map, Region.mapOp_comp]
        · exact lawfulReductFunctor_comp h k }

/-- Observational λRTL judgements over pair-lawful models. -/
def rtlObsLRoom (R : M (L × α) → M (L × α) → Prop) (S : Sig) : Room.{0, 0, 0} where
  Sen := Judgement V L S.ops
  Mod := Cat.of (Discrete (LawfulModel M α S.ops))
  Sat m j := ∀ σ : V → α, R (j.lhs.evalObs m.as.1 σ) (j.rhs.evalObs m.as.1 σ)

/-- The observational λRTL institution over pair-lawful models. -/
def rtlObsL (R : M (L × α) → M (L × α) → Prop) : Inst.{1, 0, 0, 0, 0} where
  Sign := Sig
  I :=
    { obj := rtlObsLRoom V L M α R
      map {S S'} h :=
        ⟨Judgement.map h, lawfulReductFunctor h, fun m j => by
          change (∀ σ, R ((j.lhs.mapOp h).evalObs m.as.1 σ) ((j.rhs.mapOp h).evalObs m.as.1 σ)) ↔
            ∀ σ, R (j.lhs.evalObs (m.as.1.reduct h) σ) (j.rhs.evalObs (m.as.1.reduct h) σ)
          simp only [Region.evalObs_mapOp]⟩
      map_id S := by
        apply Room.hom_ext
        · funext j
          change Judgement.map id j = j
          cases j with | mk Γ r r' =>
          simp only [Judgement.map, Region.mapOp_id]
        · exact lawfulReductFunctor_id S.ops
      map_comp {S S' S''} h k := by
        apply Room.hom_ext
        · funext j
          change Judgement.map (k ∘ h) j = Judgement.map k (Judgement.map h j)
          cases j with | mk Γ r r' =>
          simp only [Judgement.map, Region.mapOp_comp]
        · exact lawfulReductFunctor_comp h k }

variable {V L M α}

/-- Versioning a λRTL judgement. -/
def Judgement.version {F : Type} (j : Judgement V L F) : SSAJudgement (V × ℕ) L F :=
  ⟨⟨initCtx j.lhs ∪ initCtx j.rhs, versionTop j.lhs, versionTop j.rhs⟩,
    versionTop_isSSA_of _ _
      (fun p hp => by
        simp only [initCtx, Finset.mem_union, List.mem_toFinset, List.mem_map] at hp
        rcases hp with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl)
      (fun y hy => Finset.mem_union_left _ (by
        simp only [initCtx, List.mem_toFinset, List.mem_map]; exact ⟨y, hy, rfl⟩)),
    versionTop_isSSA_of _ _
      (fun p hp => by
        simp only [initCtx, Finset.mem_union, List.mem_toFinset, List.mem_map] at hp
        rcases hp with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl)
      (fun y hy => Finset.mem_union_right _ (by
        simp only [initCtx, List.mem_toFinset, List.mem_map]; exact ⟨y, hy, rfl⟩))⟩

variable (V L M α) [LawfulMonad M]

/-- The versioning corridor at one signature. -/
def versionCorridor (R : M (L × α) → M (L × α) → Prop) (S : Sig) :
    rtlObsLRoom V L M α R S ⟶ ssaLRoom (V × ℕ) L M α R S :=
  ⟨Judgement.version, 𝟭 _, fun m j => by
    change (∀ ρ : V × ℕ → α, R ((versionTop j.lhs).evalSSA m.as.1 ρ)
        ((versionTop j.rhs).evalSSA m.as.1 ρ)) ↔
      ∀ σ : V → α, R (j.lhs.evalObs m.as.1 σ) (j.rhs.evalObs m.as.1 σ)
    constructor
    · intro H σ
      have := H (fun p => σ p.1)
      rwa [versionTop_evalSSA m.as.1 m.as.2 j.lhs σ _ (fun _ => rfl),
        versionTop_evalSSA m.as.1 m.as.2 j.rhs σ _ (fun _ => rfl)] at this
    · intro H ρ
      rw [versionTop_evalSSA m.as.1 m.as.2 j.lhs (fun y => ρ (y, 0)) ρ (fun _ => rfl),
        versionTop_evalSSA m.as.1 m.as.2 j.rhs (fun y => ρ (y, 0)) ρ (fun _ => rfl)]
      exact H _⟩

/-- **Comorphism** `λRTL → λSSA` by versioning (pair-lawful models): a λRTL judgement holds
in a model iff its versioned λSSA judgement does. -/
def versionCoHom (R : M (L × α) → M (L × α) → Prop) :
    Inst.CoHom (rtlObsL V L M α R) (ssaL (V × ℕ) L M α R) where
  Φ := 𝟭 Sig
  ρ :=
    { app := versionCorridor V L M α R
      naturality := by
        intro S S' h
        apply Room.hom_ext
        · funext j
          change Judgement.version (Judgement.map h j) = SSAJudgement.map h (Judgement.version j)
          cases j with | mk Γ r r' =>
          have e1 := initCtx_mapOp (L := L) (F := S.ops) (F' := S'.ops) h r
          have e2 := initCtx_mapOp (L := L) (F := S.ops) (F' := S'.ops) h r'
          have e3 := versionTop_mapOp (F := S.ops) (F' := S'.ops) h r
          have e4 := versionTop_mapOp (F := S.ops) (F' := S'.ops) h r'
          simp only [Judgement.version, Judgement.map, SSAJudgement.map, e1, e2, e3, e4]
        · exact CategoryTheory.Functor.ext (fun m => by cases m; rfl) }

end Silmaril.SSA.LambdaRTL.Institution
