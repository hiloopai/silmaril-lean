module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Associativity
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ContextCoherence

/-! # Copying a context component across a split -/

@[expose] public section

-- Toolchain fix (port): Mathlib's `β_` and the premonoidal `β_` of
-- `Premonoidal.Symmetric` are both in scope; select Mathlib's braiding, as in the source.
local notation (priority := high) "β_" => CategoryTheory.BraidedCategory.braiding
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Structural
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalCategory
universe u v
variable {K : Type u} [Category.{v} K] [MonoidalCategory K] [SymmetricCategory K]

/-- Copying the moved component distributes it to both outputs. -/
theorem moveLeft_distribute (L R C : K) (c : C ⟶ C ⊗ C) :
    (α_ L R C).hom ≫ L ◁ (β_ R C).hom ≫ (α_ L C R).inv ≫
      (L ◁ c) ▷ R ≫ (α_ L C C).inv ▷ R ≫
      (α_ (L ⊗ C) C R).hom ≫ (L ⊗ C) ◁ (β_ C R).hom =
    (L ⊗ R) ◁ c ≫ tensorμ L R C C := by
  simp only [tensorμ]
  simp
  simp only [← whiskerLeft_comp_assoc]
  rw [← braiding_naturality_right_assoc]
  simp [braiding_tensor_right_hom]
  simp only [← whiskerLeft_comp_assoc, ← whiskerLeft_comp, SymmetricCategory.symmetry,
    whiskerLeft_id, Category.id_comp]

/-- A three-way splitting diagram distributes a duplicable component. -/
theorem distribute_diagram {G AB L R C X X' Y : K}
    (s : G ⟶ AB ⊗ C) (t : AB ⟶ L ⊗ R) (c : C ⟶ C ⊗ C)
    (p : G ⟶ X ⊗ R) (q : X ⟶ L ⊗ C)
    (q1 : X ⟶ X' ⊗ C) (l : X' ⟶ L ⊗ C)
    (hp : G ⟶ X' ⊗ Y) (v : Y ⟶ C ⊗ R)
    (ha : q1 ≫ l ▷ C = q ≫ L ◁ c ≫ (α_ L C C).inv)
    (hb : s ≫ t ▷ C ≫ (α_ L R C).hom ≫ L ◁ (β_ R C).hom ≫ (α_ L C R).inv = p ≫ q ▷ R)
    (hc : p ≫ q1 ▷ R ≫ (α_ X' C R).hom = hp ≫ X' ◁ v) :
    s ≫ (t ⊗ₘ c) ≫ tensorμ L R C C = hp ≫ (l ⊗ₘ (v ≫ (β_ C R).hom)) := by
  symm
  rw [tensorHom_def', whiskerLeft_comp]
  simp only [Category.assoc]
  rw [whisker_exchange]
  rw [← reassoc_of% hc, ← associator_naturality_left_assoc]
  rw [← comp_whiskerRight_assoc, ha]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← reassoc_of% hb, moveLeft_distribute]
  rw [tensorHom_def]
  simp only [Category.assoc]

end Silmaril.Isotope.Refinement.Models.Structural

namespace Silmaril.Isotope.Refinement.Models.Denotation
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Native reassociation with an exchange has the expected pure wire map. -/
theorem splitPure_swapAssoc {n : Nat} {Γ Γab Γa Γb Γc Γac : QCtx τ n}
    (s : Γ.Split Γab Γc) (t : Γab.Split Γa Γb)
    (p : Γ.Split Γac Γb) (q : Γac.Split Γa Γc) :
    let G : M.PureObject := ⟨packed Γ⟩
    let AB : M.PureObject := ⟨packed Γab⟩
    let A : M.PureObject := ⟨packed Γa⟩
    let B : M.PureObject := ⟨packed Γb⟩
    let C : M.PureObject := ⟨packed Γc⟩
    let AC : M.PureObject := ⟨packed Γac⟩
    let ss : G ⟶ AB ⊗ C := splitPure M s
    let tt : AB ⟶ A ⊗ B := splitPure M t
    let pp : G ⟶ AC ⊗ B := splitPure M p
    let qq : AC ⟶ A ⊗ C := splitPure M q
    ss ≫ tt ▷ C ≫ (α_ A B C).hom ≫ A ◁ (β_ B C).hom ≫ (α_ A C B).inv = pp ≫ qq ▷ B := by
  dsimp only
  let G : M.PureObject := ⟨packed Γ⟩
  let AB : M.PureObject := ⟨packed Γab⟩
  let A : M.PureObject := ⟨packed Γa⟩
  let B : M.PureObject := ⟨packed Γb⟩
  let C : M.PureObject := ⟨packed Γc⟩
  let AC : M.PureObject := ⟨packed Γac⟩
  let ss : G ⟶ AB ⊗ C := splitPure M s
  let tt : AB ⟶ A ⊗ B := splitPure M t
  let pp : G ⟶ AC ⊗ B := splitPure M p
  let qq : AC ⟶ A ⊗ C := splitPure M q
  change ss ≫ tt ▷ C ≫ (α_ A B C).hom ≫ A ◁ (β_ B C).hom ≫ (α_ A C B).inv = pp ≫ qq ▷ B
  apply (cancel_mono (β_ (A ⊗ C) B).hom).mp
  simp only [Category.assoc]
  rw [Structural.moveLeft_braid]
  rw [← comp_whiskerRight_assoc]
  have ht : tt ≫ (β_ A B).hom = splitPure M t.symm := splitPure_symm M t
  rw [ht, BraidedCategory.braiding_naturality_left]
  have hp : pp ≫ (β_ AC B).hom = splitPure M p.symm := splitPure_symm M p
  rw [← Category.assoc pp, hp]
  exact splitPure_assoc M s t.symm p.symm q

/-- The exchanged reassociation law on normalized model arrows. -/
theorem split_swapAssoc {n : Nat} {Γ Γab Γa Γb Γc Γac : QCtx τ n}
    (s : Γ.Split Γab Γc) (t : Γab.Split Γa Γb)
    (p : Γ.Split Γac Γb) (q : Γac.Split Γa Γc) :
    M.compose (split M s) (M.compose (M.right (split M t) (packed Γc))
      (M.compose (M.associator (packed Γa) (packed Γb) (packed Γc))
        (M.compose (M.left (packed Γa) (M.braiding (packed Γb) (packed Γc)))
          (M.associatorInv (packed Γa) (packed Γc) (packed Γb))))) =
    M.compose (split M p) (M.right (split M q) (packed Γb)) :=
  congrArg Subtype.val (splitPure_swapAssoc M s t p q)

/-- Distributing a relevant context across a split agrees with copying it once
and routing its two copies to the outputs. The witnesses are constructed together. -/
theorem split_distribute (N : SeqModel.{u,v,w,r} τ Φ ε)
    {n : Nat} {Γ Γab Γa Γb Γc : QCtx τ n}
    (s : Γ.Split Γab Γc) (t : Γab.Split Γa Γb)
    (hc : Quantity.relevant ≤ Γc.linearity) :
    ∃ Γac Γbc, ∃ (p : Γ.Split Γac Γbc) (l : Γac.Split Γa Γc) (r : Γbc.Split Γb Γc),
      N.compose (split N.toSeqData s)
        (N.compose (N.tensor (split N.toSeqData t)
          (N.copy (packed Γc) (hc.trans (packed_quantity Γc))))
          (N.middleSwap (packed Γa) (packed Γb) (packed Γc) (packed Γc))) =
      N.compose (split N.toSeqData p) (N.tensor (split N.toSeqData l) (split N.toSeqData r)) := by
  obtain ⟨X, p, q⟩ := s.swapAssoc t
  obtain ⟨X', q1, l⟩ := q.assoc (QCtx.Split.diagonal Γc hc)
  obtain ⟨Y, hp, v⟩ := p.swapAssoc q1.symm
  refine ⟨X', Y, hp.symm, l, v.symm, ?_⟩
  let L : N.toSeqData.PureObject := ⟨packed Γa⟩
  let R : N.toSeqData.PureObject := ⟨packed Γb⟩
  let C : N.toSeqData.PureObject := ⟨packed Γc⟩
  let XX : N.toSeqData.PureObject := ⟨packed X⟩
  let XX' : N.toSeqData.PureObject := ⟨packed X'⟩
  let YY : N.toSeqData.PureObject := ⟨packed Y⟩
  let cc : C ⟶ C ⊗ C := splitPure N.toSeqData (QCtx.Split.diagonal Γc hc)
  let qq : XX ⟶ L ⊗ C := splitPure N.toSeqData q
  let qq1 : XX ⟶ XX' ⊗ C := splitPure N.toSeqData q1
  let ll : XX' ⟶ L ⊗ C := splitPure N.toSeqData l
  let vv : YY ⟶ C ⊗ R := splitPure N.toSeqData v
  have ha : qq1 ≫ ll ▷ C = qq ≫ L ◁ cc ≫ (α_ L C C).inv := by
    apply (cancel_mono (α_ L C C).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact splitPure_assoc N.toSeqData q1 l q (QCtx.Split.diagonal Γc hc)
  have he := Structural.distribute_diagram
    (show (⟨packed Γ⟩ : N.toSeqData.PureObject) ⟶ (⟨packed Γab⟩ : N.toSeqData.PureObject) ⊗ C from splitPure N.toSeqData s)
    (show (⟨packed Γab⟩ : N.toSeqData.PureObject) ⟶ L ⊗ R from splitPure N.toSeqData t) cc
    (show (⟨packed Γ⟩ : N.toSeqData.PureObject) ⟶ XX ⊗ R from splitPure N.toSeqData p) qq qq1 ll
    (show (⟨packed Γ⟩ : N.toSeqData.PureObject) ⟶ XX' ⊗ YY from splitPure N.toSeqData hp.symm) vv ha
    (splitPure_swapAssoc N.toSeqData s t p q)
    (splitPure_assoc N.toSeqData p q1 hp.symm v)
  have hv : vv ≫ (β_ C R).hom = splitPure N.toSeqData v.symm := splitPure_symm N.toSeqData v
  rw [hv] at he
  have hval := congrArg Subtype.val he
  change N.compose (split N.toSeqData s)
    (N.compose (N.tensor (split N.toSeqData t)
      (split N.toSeqData (QCtx.Split.diagonal Γc hc)))
      (N.middleSwap (packed Γa) (packed Γb) (packed Γc) (packed Γc))) =
    N.compose (split N.toSeqData hp.symm)
      (N.tensor (split N.toSeqData l) (split N.toSeqData v.symm)) at hval
  rw [split_diagonal N Γc hc] at hval
  exact hval

end Silmaril.Isotope.Refinement.Models.Denotation
