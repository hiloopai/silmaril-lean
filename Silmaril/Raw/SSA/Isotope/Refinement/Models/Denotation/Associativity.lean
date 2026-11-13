module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Slots

@[expose] public section

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory
open scoped MonoidalCategory
universe u v w r
namespace Structural
open MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

theorem split_right_unit {X Y Z : C} (f : X ⟶ Y ⊗ Z) :
    (ρ_ X).inv ≫ f ▷ (𝟙_ C) ≫ (α_ Y Z (𝟙_ C)).hom = f ≫ Y ◁ (ρ_ Z).inv := by
  rw [← rightUnitor_inv_naturality_assoc]
  congr 1
  monoidal

theorem split_left_unit {X Y Z : C} (f : X ⟶ Y ⊗ Z) :
    f ≫ (λ_ Y).inv ▷ Z ≫ (α_ (𝟙_ C) Y Z).hom = (λ_ X).inv ≫ (𝟙_ C) ◁ f := by
  rw [← leftUnitor_inv_naturality]
  congr 1
  monoidal

theorem split_middle_unit {X Y Z : C} (f : X ⟶ Y ⊗ Z) :
    f ≫ (ρ_ Y).inv ▷ Z ≫ (α_ Y (𝟙_ C) Z).hom = f ≫ Y ◁ (λ_ Z).inv := by
  congr 1
  monoidal



/-- Coherence of an associative split survives a change of packing convention. -/
theorem split_assoc_iso {L B D E G H L' B' D' E' G' H' : C}
    (iL : L' ≅ L) (iB : B' ≅ B) (iD : D' ≅ D) (iE : E' ≅ E) (iG : G' ≅ G) (iH : H' ≅ H)
    (f : L ⟶ B ⊗ G) (g : B ⟶ D ⊗ E) (f' : L ⟶ D ⊗ H) (g' : H ⟶ E ⊗ G)
    (hf : f ≫ g ▷ G ≫ (α_ D E G).hom = f' ≫ D ◁ g') :
    (iL.hom ≫ f ≫ (iB.inv ⊗ₘ iG.inv)) ≫
      (iB.hom ≫ g ≫ (iD.inv ⊗ₘ iE.inv)) ▷ G' ≫ (α_ D' E' G').hom =
    (iL.hom ≫ f' ≫ (iD.inv ⊗ₘ iH.inv)) ≫ D' ◁ (iH.hom ≫ g' ≫ (iE.inv ⊗ₘ iG.inv)) := by
  simp only [Category.assoc, comp_whiskerRight, whiskerLeft_comp]
  simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Iso.inv_hom_id_assoc, Category.comp_id]
  rw [tensorHom_def (g ≫ (iD.inv ⊗ₘ iE.inv)) iG.inv, comp_whiskerRight]
  simp only [Category.assoc]
  rw [← tensorHom_def_assoc, associator_naturality]
  rw [tensorHom_def' iD.inv g']
  simp only [Category.assoc]
  rw [id_tensorHom, ← tensorHom_def, ← reassoc_of% hf]

variable [SymmetricCategory C]

/-- Naturality of the tensor comparison in a split of its first output. -/
@[reassoc] theorem tensorSplit_left {L B D E G S T U V W : C}
    (f : L ⟶ B ⊗ G) (g : B ⟶ D ⊗ E)
    (h : S ⟶ T ⊗ W) (k : T ⟶ U ⊗ V) :
    (f ⊗ₘ h) ≫ tensorμ B G T W ≫ ((g ⊗ₘ k) ≫ tensorμ D E U V) ▷ (G ⊗ W) =
      ((f ≫ g ▷ G) ⊗ₘ (h ≫ k ▷ W)) ≫
        tensorμ (D ⊗ E) G (U ⊗ V) W ≫ tensorμ D E U V ▷ (G ⊗ W) := by
  have hn := tensorμ_natural g (𝟙 G) k (𝟙 W)
  simp only [tensorHom_id, id_whiskerRight] at hn
  simp only [comp_whiskerRight]
  rw [← reassoc_of% hn, tensorHom_comp_tensorHom_assoc]


/-- Naturality of the tensor comparison in a split of its second output. -/
@[reassoc] theorem tensorSplit_right {L B D E G S T U V W : C}
    (f : L ⟶ D ⊗ B) (g : B ⟶ E ⊗ G)
    (h : S ⟶ U ⊗ T) (k : T ⟶ V ⊗ W) :
    (f ⊗ₘ h) ≫ tensorμ D B U T ≫ (D ⊗ U) ◁ ((g ⊗ₘ k) ≫ tensorμ E G V W) =
      ((f ≫ D ◁ g) ⊗ₘ (h ≫ U ◁ k)) ≫
        tensorμ D (E ⊗ G) U (V ⊗ W) ≫ (D ⊗ U) ◁ tensorμ E G V W := by
  have hn := tensorμ_natural (𝟙 D) g (𝟙 U) k
  simp only [id_tensorHom, whiskerLeft_id] at hn
  simp only [whiskerLeft_comp]
  rw [← reassoc_of% hn, tensorHom_comp_tensorHom_assoc]

/-- Tensoring two associative splitting diagrams gives an associative diagram. -/
theorem tensorSplit_assoc {L B D E G H S T U V W Z : C}
    (f : L ⟶ B ⊗ G) (g : B ⟶ D ⊗ E) (f' : L ⟶ D ⊗ H) (g' : H ⟶ E ⊗ G)
    (h : S ⟶ T ⊗ W) (k : T ⟶ U ⊗ V) (h' : S ⟶ U ⊗ Z) (k' : Z ⟶ V ⊗ W)
    (hf : f ≫ g ▷ G ≫ (α_ D E G).hom = f' ≫ D ◁ g')
    (hh : h ≫ k ▷ W ≫ (α_ U V W).hom = h' ≫ U ◁ k') :
    (f ⊗ₘ h) ≫ tensorμ B G T W ≫ ((g ⊗ₘ k) ≫ tensorμ D E U V) ▷ (G ⊗ W) ≫
      (α_ (D ⊗ U) (E ⊗ V) (G ⊗ W)).hom =
    (f' ⊗ₘ h') ≫ tensorμ D H U Z ≫ (D ⊗ U) ◁ ((g' ⊗ₘ k') ≫ tensorμ E G V W) := by
  rw [tensorSplit_left_assoc, tensorSplit_right, associator_monoidal]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [hf, hh]

end Structural

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace Denotation
open MonoidalCategory BraidedCategory
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- A single variable split into three outputs is independent of parenthesization. -/
theorem slotSplit_assoc {A : τ} {q q12 q3 q1 q2 q23 : Usage}
    (s : QCtx.SlotSplit A q q12 q3) (t : QCtx.SlotSplit A q12 q1 q2)
    (u : QCtx.SlotSplit A q q1 q23) (v : QCtx.SlotSplit A q23 q2 q3) :
    slotSplit M s ≫ (slotSplit M t ⊗ₘ 𝟙 (slotObject M A q3)) ≫
      (α_ (slotObject M A q1) (slotObject M A q2) (slotObject M A q3)).hom =
    slotSplit M u ≫ (𝟙 (slotObject M A q1) ⊗ₘ slotSplit M v) := by
  cases q <;> cases q12 <;> cases q3 <;> cases q1 <;> cases q2 <;> cases q23
  all_goals try (solve | cases s)
  all_goals try (solve | cases t)
  all_goals try (solve | cases u)
  all_goals try (solve | cases v)
  all_goals simp only [slotSplit, slotObject, tensorHom_id, id_tensorHom]
  all_goals try monoidal
  all_goals try exact Subtype.ext (M.copy_associator A _)
  all_goals first
    | exact Structural.split_right_unit _
    | exact Structural.split_left_unit _
    | exact Structural.split_middle_unit _


/-- Appending a quantitative slot preserves associativity of context splitting. -/
theorem splitSlot_assoc {L B12 B1 B2 B3 B23 A : τ}
    (f : PureHom M L (product B12 B3)) (g : PureHom M B12 (product B1 B2))
    (f' : PureHom M L (product B1 B23)) (g' : PureHom M B23 (product B2 B3))
    (hf : pureCompose M f (pureCompose M (pureRight M g B3)
        ⟨M.associator B1 B2 B3, M.associator_pure _ _ _⟩) =
      pureCompose M f' (pureLeft M B1 g'))
    {q q12 q3 q1 q2 q23 : Usage}
    (s : QCtx.SlotSplit A q q12 q3) (t : QCtx.SlotSplit A q12 q1 q2)
    (u : QCtx.SlotSplit A q q1 q23) (v : QCtx.SlotSplit A q23 q2 q3) :
    pureCompose M (splitSlot M f s)
      (pureCompose M (pureRight M (splitSlot M g t) (retain B3 A q3))
        ⟨M.associator (retain B1 A q1) (retain B2 A q2) (retain B3 A q3), M.associator_pure _ _ _⟩) =
      pureCompose M (splitSlot M f' u) (pureLeft M (retain B1 A q1) (splitSlot M g' v)) := by
  let ff : (⟨L⟩ : M.PureObject) ⟶ (⟨B12⟩ : M.PureObject) ⊗ (⟨B3⟩ : M.PureObject) := f
  let gg : (⟨B12⟩ : M.PureObject) ⟶ (⟨B1⟩ : M.PureObject) ⊗ (⟨B2⟩ : M.PureObject) := g
  let ff' : (⟨L⟩ : M.PureObject) ⟶ (⟨B1⟩ : M.PureObject) ⊗ (⟨B23⟩ : M.PureObject) := f'
  let gg' : (⟨B23⟩ : M.PureObject) ⟶ (⟨B2⟩ : M.PureObject) ⊗ (⟨B3⟩ : M.PureObject) := g'
  have h := Structural.tensorSplit_assoc ff gg ff' gg'
    (slotSplit M s) (slotSplit M t) (slotSplit M u) (slotSplit M v) hf (by simpa only [tensorHom_id, id_tensorHom] using slotSplit_assoc M s t u v)
  have he := Structural.split_assoc_iso
    (retainIso M L A q) (retainIso M B12 A q12) (retainIso M B1 A q1)
    (retainIso M B2 A q2) (retainIso M B3 A q3) (retainIso M B23 A q23)
    ((ff ⊗ₘ slotSplit M s) ≫ tensorμ _ _ _ _)
    ((gg ⊗ₘ slotSplit M t) ≫ tensorμ _ _ _ _)
    ((ff' ⊗ₘ slotSplit M u) ≫ tensorμ _ _ _ _)
    ((gg' ⊗ₘ slotSplit M v) ≫ tensorμ _ _ _ _) (by simpa only [Category.assoc] using h)
  change (splitSlot M f s : (⟨retain L A q⟩ : M.PureObject) ⟶ _) ≫
      (splitSlot M g t : (⟨retain B12 A q12⟩ : M.PureObject) ⟶ _) ▷ (⟨retain B3 A q3⟩ : M.PureObject) ≫
      (α_ (⟨retain B1 A q1⟩ : M.PureObject) (⟨retain B2 A q2⟩ : M.PureObject) (⟨retain B3 A q3⟩ : M.PureObject)).hom =
    (splitSlot M f' u : (⟨retain L A q⟩ : M.PureObject) ⟶ _) ≫
      (⟨retain B1 A q1⟩ : M.PureObject) ◁ (splitSlot M g' v : (⟨retain B23 A q23⟩ : M.PureObject) ⟶ _)
  simp only [ff, gg, ff', gg', Category.assoc, ← splitSlot_tensor] at he
  exact he


/-- Three-way quantitative context splitting is associative, for every choice
of intermediate quantities admitted by the native split judgment. -/
theorem splitPure_assoc {n : Nat} {Γ Γ12 Γ1 Γ2 Γ3 Γ23 : QCtx τ n}
    (s : QCtx.Split Γ Γ12 Γ3) (t : QCtx.Split Γ12 Γ1 Γ2)
    (u : QCtx.Split Γ Γ1 Γ23) (v : QCtx.Split Γ23 Γ2 Γ3) :
    pureCompose M (splitPure M s) (pureCompose M (pureRight M (splitPure M t) (packed Γ3))
      ⟨M.associator (packed Γ1) (packed Γ2) (packed Γ3), M.associator_pure _ _ _⟩) =
    pureCompose M (splitPure M u) (pureLeft M (packed Γ1) (splitPure M v)) := by
  induction Γ using QCtx.inductionOn with
  | nil =>
    change (λ_ (𝟙_ M.PureObject)).inv ≫ (λ_ (𝟙_ M.PureObject)).inv ▷ (𝟙_ M.PureObject) ≫
      (α_ (𝟙_ M.PureObject) (𝟙_ M.PureObject) (𝟙_ M.PureObject)).hom =
      (λ_ (𝟙_ M.PureObject)).inv ≫ (𝟙_ M.PureObject) ◁ (λ_ (𝟙_ M.PureObject)).inv
    monoidal
  | @snoc n Γ A q ih =>
    obtain ⟨Γ12, q12, rfl⟩ := QCtx.exists_snoc_of_type Γ12 A (s 0).1
    obtain ⟨Γ3, q3, rfl⟩ := QCtx.exists_snoc_of_type Γ3 A (s 0).2.1
    obtain ⟨Γ1, q1, rfl⟩ := QCtx.exists_snoc_of_type Γ1 A (t 0).1
    obtain ⟨Γ2, q2, rfl⟩ := QCtx.exists_snoc_of_type Γ2 A (t 0).2.1
    obtain ⟨Γ23, q23, rfl⟩ := QCtx.exists_snoc_of_type Γ23 A (u 0).2.1
    have st : QCtx.Split Γ Γ12 Γ3 := fun i => s i.succ
    have tt : QCtx.Split Γ12 Γ1 Γ2 := fun i => t i.succ
    have ut : QCtx.Split Γ Γ1 Γ23 := fun i => u i.succ
    have vt : QCtx.Split Γ23 Γ2 Γ3 := fun i => v i.succ
    exact splitSlot_assoc M (splitPure M st) (splitPure M tt) (splitPure M ut) (splitPure M vt)
      (ih st tt ut vt) (s 0).2.2 (t 0).2.2 (u 0).2.2 (v 0).2.2

/-- The model's actual associator relates the two native three-way context maps. -/
theorem split_assoc {n : Nat} {Γ Γ12 Γ1 Γ2 Γ3 Γ23 : QCtx τ n}
    (s : QCtx.Split Γ Γ12 Γ3) (t : QCtx.Split Γ12 Γ1 Γ2)
    (u : QCtx.Split Γ Γ1 Γ23) (v : QCtx.Split Γ23 Γ2 Γ3) :
    M.compose (split M s) (M.compose (M.right (split M t) (packed Γ3))
      (M.associator (packed Γ1) (packed Γ2) (packed Γ3))) =
    M.compose (split M u) (M.left (packed Γ1) (split M v)) :=
  congrArg Subtype.val (splitPure_assoc M s t u v)

end Denotation
end Silmaril.Isotope.Refinement.Models
