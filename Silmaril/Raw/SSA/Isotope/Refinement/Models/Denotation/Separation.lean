module

public import Silmaril.Raw.SSA.Isotope.Refinement.ContextRetention
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Associativity

/-! # Disjoint context splits are pure isomorphisms -/

@[expose] public section

-- Toolchain fix (port): Mathlib's `β_` and the premonoidal `β_` of
-- `Premonoidal.Symmetric` are both in scope; select Mathlib's braiding, as in the source.
local notation (priority := high) "β_" => CategoryTheory.BraidedCategory.braiding
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
open CategoryTheory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

theorem splitSlot_isIso {L B D A : τ} (f : PureHom M L (product B D))
    {q ql qr : Usage} (h : QCtx.SlotSplit A q ql qr) (hd : ql = .zero ∨ qr = .zero)
    (hf : IsIso (show (⟨L⟩ : M.PureObject) ⟶ ⟨product B D⟩ from f)) :
    IsIso (show (⟨retain L A q⟩ : M.PureObject) ⟶
      ⟨product (retain B A ql) (retain D A qr)⟩ from splitSlot M f h) := by
  let L' : M.PureObject := ⟨L⟩
  let B' : M.PureObject := ⟨B⟩
  let D' : M.PureObject := ⟨D⟩
  let A' : M.PureObject := ⟨A⟩
  let ff : L' ⟶ B' ⊗ D' := f
  let : IsIso ff := hf
  cases q <;> cases ql <;> cases qr
  · exact hf
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · change IsIso (ff ▷ A' ≫ (α_ B' D' A').hom)
    infer_instance
  · change IsIso (ff ▷ A' ≫ (α_ B' D' A').hom ≫ B' ◁ (β_ D' A').hom ≫ (α_ B' A' D').inv)
    infer_instance
  · rcases hd with hd | hd <;> cases hd

/-- Separating resources without copying uses only tensor coherence maps. -/
theorem splitPure_isIso {n : Nat} {Γ Γl Γr : QCtx τ n}
    (h : Γ.Split Γl Γr) (hd : h.Disjoint) :
    IsIso (show (⟨packed Γ⟩ : M.PureObject) ⟶
      ⟨product (packed Γl) (packed Γr)⟩ from splitPure M h) := by
  induction Γ using QCtx.inductionOn with
  | nil =>
    change IsIso (λ_ (𝟙_ M.PureObject)).inv
    infer_instance
  | @snoc n Γ A q ih =>
    obtain ⟨Γl, ql, rfl⟩ := QCtx.exists_snoc_of_type Γl A (h 0).1
    obtain ⟨Γr, qr, rfl⟩ := QCtx.exists_snoc_of_type Γr A (h 0).2.1
    have ht : Γ.Split Γl Γr := fun i => h i.succ
    have hdt : ht.Disjoint := fun i => hd i.succ
    exact splitSlot_isIso M (splitPure M ht) (h 0).2.2 (hd 0) (ih ht hdt)

/-- Recombine a disjoint split with its inverse pure structural map. -/
def unsplitPure {n : Nat} {Γ Γl Γr : QCtx τ n} (h : Γ.Split Γl Γr) (hd : h.Disjoint) :
    PureHom M (product (packed Γl) (packed Γr)) (packed Γ) := by
  let f : (⟨packed Γ⟩ : M.PureObject) ⟶ ⟨product (packed Γl) (packed Γr)⟩ := splitPure M h
  let : IsIso f := splitPure_isIso M h hd
  exact inv f

theorem split_unsplit {n : Nat} {Γ Γl Γr : QCtx τ n} (h : Γ.Split Γl Γr) (hd : h.Disjoint) :
    M.compose (split M h) (unsplitPure M h hd).val = M.identity (packed Γ) := by
  let f : (⟨packed Γ⟩ : M.PureObject) ⟶ ⟨product (packed Γl) (packed Γr)⟩ := splitPure M h
  let : IsIso f := splitPure_isIso M h hd
  exact congrArg Subtype.val (IsIso.hom_inv_id f)

theorem unsplit_split {n : Nat} {Γ Γl Γr : QCtx τ n} (h : Γ.Split Γl Γr) (hd : h.Disjoint) :
    M.compose (unsplitPure M h hd).val (split M h) = M.identity (product (packed Γl) (packed Γr)) := by
  let f : (⟨packed Γ⟩ : M.PureObject) ⟶ ⟨product (packed Γl) (packed Γr)⟩ := splitPure M h
  let : IsIso f := splitPure_isIso M h hd
  exact congrArg Subtype.val (IsIso.inv_hom_id f)

end Silmaril.Isotope.Refinement.Models.Denotation
