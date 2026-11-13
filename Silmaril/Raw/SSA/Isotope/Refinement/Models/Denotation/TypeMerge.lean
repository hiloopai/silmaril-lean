module

public import Silmaril.Raw.SSA.Isotope.Refinement.TypeMerge
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Effects
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ControlCoherence
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ContextCoherence

/-! # Pure comparison maps for hidden free-type choices -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} (Ty α) Φ ε)

def pureIdentity (A : Ty α) : PureHom M.toSeqData A A :=
  ⟨M.identity A, M.toSeqData.identity_effect ⊥ A⟩

def pureInl (A B : Ty α) : PureHom M.toSeqData A (Ty.coprod A B) :=
  ⟨M.inl A B, M.inl_pure A B⟩

def pureInr (A B : Ty α) : PureHom M.toSeqData B (Ty.coprod A B) :=
  ⟨M.inr A B, M.inr_pure A B⟩

/-- The covariant action of the chosen coproduct on pure maps. -/
def pureSum {A B C D : Ty α} (f : PureHom M.toSeqData A C) (g : PureHom M.toSeqData B D) :
    PureHom M.toSeqData (Ty.coprod A B) (Ty.coprod C D) :=
  ⟨M.desc (M.compose f.1 (M.inl C D)) (M.compose g.1 (M.inr C D)),
    M.desc_effect (M.toSeqData.compose_effect f.2 (M.inl_pure C D))
      (M.toSeqData.compose_effect g.2 (M.inr_pure C D))⟩

@[simp] theorem pureSum_identity (A B : Ty α) :
    pureSum M (pureIdentity M A) (pureIdentity M B) = pureIdentity M (.coprod A B) := by
  apply Subtype.ext
  apply M.sum_hom_ext
  · simp only [pureSum, pureIdentity, M.inl_desc]
    exact (M.toSeqData.identity_compose _).trans (M.toSeqData.compose_identity _).symm
  · simp only [pureSum, pureIdentity, M.inr_desc]
    exact (M.toSeqData.identity_compose _).trans (M.toSeqData.compose_identity _).symm

@[simp] theorem pureTensor_identity (A B : Ty α) :
    pureTensor M.toSeqData (pureIdentity M A) (pureIdentity M B) = pureIdentity M (.product A B) := by
  apply Subtype.ext
  change M.tensor (M.identity A) (M.identity B) = M.identity (product A B)
  rw [SeqData.tensor, M.toSeqData.right_identity, M.toSeqData.left_identity, M.toSeqData.identity_compose]

theorem pureTensor_target_heq {A B C D C' D' : Ty α} (hC : C = C') (hD : D = D')
    {f : PureHom M.toSeqData A C} {f' : PureHom M.toSeqData A C'}
    {g : PureHom M.toSeqData B D} {g' : PureHom M.toSeqData B D'} (hf : HEq f f') (hg : HEq g g') :
    HEq (pureTensor M.toSeqData f g) (pureTensor M.toSeqData f' g') := by
  cases hC
  cases hD
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

theorem pureSum_target_heq {A B C D C' D' : Ty α} (hC : C = C') (hD : D = D')
    {f : PureHom M.toSeqData A C} {f' : PureHom M.toSeqData A C'}
    {g : PureHom M.toSeqData B D} {g' : PureHom M.toSeqData B D'} (hf : HEq f f') (hg : HEq g g') :
    HEq (pureSum M f g) (pureSum M f' g') := by
  cases hC
  cases hD
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

theorem purePair_components_heq {A C D : Ty α} (he : C = D)
    {f : PureHom M.toSeqData A C × PureHom M.toSeqData A C}
    {g : PureHom M.toSeqData A D × PureHom M.toSeqData A D} (h : HEq f g) :
    HEq f.1 g.1 ∧ HEq f.2 g.2 := by
  cases he
  cases eq_of_heq h
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem purePair_heq {A C D : Ty α} (he : C = D)
    {f g : PureHom M.toSeqData A C} {f' g' : PureHom M.toSeqData A D}
    (hf : HEq f f') (hg : HEq g g') : HEq (f, g) (f', g') := by
  cases he
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

variable [DecidableEq α]

/-- Both input types have pure maps into their common covariant target. -/
def mergeArrows : (A B : Ty α) →
    PureHom M.toSeqData A (mergeType A B) × PureHom M.toSeqData B (mergeType A B) := by
  intro A
  induction A with
  | base a =>
    intro B
    cases B with
    | base b =>
      simp only [mergeType]
      split_ifs with he
      · subst b
        exact ⟨pureIdentity M _, pureIdentity M _⟩
      · exact ⟨pureInl M _ _, pureInr M _ _⟩
    | product | unit | coprod | empty => exact ⟨pureInl M _ _, pureInr M _ _⟩
  | unit =>
    intro B
    cases B with
    | unit => exact ⟨pureIdentity M _, pureIdentity M _⟩
    | base | product | coprod | empty => exact ⟨pureInl M _ _, pureInr M _ _⟩
  | empty =>
    intro B
    cases B with
    | empty => exact ⟨pureIdentity M _, pureIdentity M _⟩
    | base | product | unit | coprod => exact ⟨pureInl M _ _, pureInr M _ _⟩
  | product A C ihA ihC =>
    intro B
    cases B with
    | product B D =>
      exact ⟨pureTensor M.toSeqData (ihA B).1 (ihC D).1,
        pureTensor M.toSeqData (ihA B).2 (ihC D).2⟩
    | base | unit | coprod | empty => exact ⟨pureInl M _ _, pureInr M _ _⟩
  | coprod A C ihA ihC =>
    intro B
    cases B with
    | coprod B D => exact ⟨pureSum M (ihA B).1 (ihC D).1, pureSum M (ihA B).2 (ihC D).2⟩
    | base | product | unit | empty => exact ⟨pureInl M _ _, pureInr M _ _⟩

/-- Comparing a type with itself gives the identity on both sides. -/
theorem mergeArrows_self (A : Ty α) :
    HEq (mergeArrows M A A) (pureIdentity M A, pureIdentity M A) := by
  induction A with
  | base a =>
    simp only [mergeArrows, dite_true]
    exact cast_heq _ _
  | unit => rfl
  | empty => rfl
  | product A B iha ihb =>
    have ha := purePair_components_heq M (mergeType_self A) iha
    have hb := purePair_components_heq M (mergeType_self B) ihb
    change HEq
      (pureTensor M.toSeqData (mergeArrows M A A).1 (mergeArrows M B B).1,
        pureTensor M.toSeqData (mergeArrows M A A).2 (mergeArrows M B B).2) _
    exact purePair_heq M (mergeType_self (.product A B))
      ((pureTensor_target_heq M (mergeType_self A) (mergeType_self B) ha.1 hb.1).trans
        (heq_of_eq (pureTensor_identity M A B)))
      ((pureTensor_target_heq M (mergeType_self A) (mergeType_self B) ha.2 hb.2).trans
        (heq_of_eq (pureTensor_identity M A B)))
  | coprod A B iha ihb =>
    have ha := purePair_components_heq M (mergeType_self A) iha
    have hb := purePair_components_heq M (mergeType_self B) ihb
    change HEq
      (pureSum M (mergeArrows M A A).1 (mergeArrows M B B).1,
        pureSum M (mergeArrows M A A).2 (mergeArrows M B B).2) _
    exact purePair_heq M (mergeType_self (.coprod A B))
      ((pureSum_target_heq M (mergeType_self A) (mergeType_self B) ha.1 hb.1).trans
        (heq_of_eq (pureSum_identity M A B)))
      ((pureSum_target_heq M (mergeType_self A) (mergeType_self B) ha.2 hb.2).trans
        (heq_of_eq (pureSum_identity M A B)))

def mergeLeft (A B : Ty α) : M.Hom A (mergeType A B) := (mergeArrows M A B).1.1

def mergeRight (A B : Ty α) : M.Hom B (mergeType A B) := (mergeArrows M A B).2.1

theorem mergeLeft_pure (A B : Ty α) : M.hasEffect ⊥ (mergeLeft M A B) := (mergeArrows M A B).1.2

theorem mergeRight_pure (A B : Ty α) : M.hasEffect ⊥ (mergeRight M A B) := (mergeArrows M A B).2.2

end Silmaril.Isotope.Refinement.Models.Denotation
