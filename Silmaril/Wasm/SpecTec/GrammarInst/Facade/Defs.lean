module

public import Silmaril.Wasm.SpecTec.GrammarInst.CoHom.Thms

/-!
# A facade for the grammar institutions

`GrammarInst.inst A D` (grammars over the attribute algebra `A`, signatures with declarations in
`D`) and its sub-institution `instIn B g D` are bundled `Silmaril.Logic.Institution.Inst`s. This
module gives the unfolding lemmas under which `simp` reads them, and those of the comorphism
`fullCoHom` (`Silmaril.Wasm.SpecTec.GrammarInst.CoHom.Thms`):

* `inst_sat_iff`, `inst_map_sen`, `inst_map_mod_obj` (`@[simp]`, `rfl`): satisfaction is
  `Sen.Holds`, sentence translation is `Sen.rename`, the reduct precomposes;
* the same for `instIn` (`instIn_sat_iff`, `instIn_map_sen`);
* `fullCoHom_Φ`, `fullCoHom_sen`, `fullCoHom_mod_obj`, `fullCoHom_holds_iff`;
* `inst_entails_iff`: entailment in `inst A D` at a signature is entailment in the room of its
  nonterminals (`room A S.N`), the form in which the defect theorems are stated.

New lemmas; the institutions are unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open CategoryTheory Silmaril.Logic.Institution

variable {α β D : Type}

/-! ## `inst A D` -/

/-- Satisfaction in `inst A D` is `Sen.Holds`. -/
@[simp] theorem inst_sat_iff (A : Silmaril.SpecTec.Grammar.Attr α) {S : Sig D} (M : Model S.N α)
    (φ : Sen S.N α) : ((inst A D).I.obj S).Sat M φ ↔ φ.Holds A M.rel := Iff.rfl

/-- Sentence translation in `inst A D` is `Sen.rename` along the renaming. -/
@[simp] theorem inst_map_sen (A : Silmaril.SpecTec.Grammar.Attr α) {S T : Sig D} (σ : S ⟶ T)
    (φ : Sen S.N α) : ((inst A D).I.map σ).sen φ = φ.rename σ.map := rfl

/-- The reduct of `inst A D` precomposes with the renaming. -/
@[simp] theorem inst_map_mod_obj (A : Silmaril.SpecTec.Grammar.Attr α) {S T : Sig D}
    (σ : S ⟶ T) (M : Model T.N α) :
    ((inst A D).I.map σ).mod.obj M = ⟨M.rel ∘ σ.map⟩ := rfl

/-- Entailment in `inst A D` at `S` is entailment in the room of the nonterminals of `S`. -/
theorem inst_entails_iff (A : Silmaril.SpecTec.Grammar.Attr α) (S : Sig D)
    (Γ : Set (Sen S.N α)) (φ : Sen S.N α) :
    ((inst A D).I.obj S).Entails Γ φ ↔ (room A S.N).Entails Γ φ := Iff.rfl

/-! ## `instIn B g D` -/

/-- Satisfaction in `instIn B g D` is `Sen.Holds` of the underlying model. -/
@[simp] theorem instIn_sat_iff (B : Silmaril.SpecTec.Grammar.Attr β) (g : α → β) {S : Sig D}
    (M : SModel g S.N) (φ : Sen S.N β) :
    ((instIn B g D).I.obj S).Sat M φ ↔ φ.Holds B M.1.rel := Iff.rfl

/-- Sentence translation in `instIn B g D` is `Sen.rename`. -/
@[simp] theorem instIn_map_sen (B : Silmaril.SpecTec.Grammar.Attr β) (g : α → β) {S T : Sig D}
    (σ : S ⟶ T) (φ : Sen S.N β) : ((instIn B g D).I.map σ).sen φ = φ.rename σ.map := rfl

/-! ## The full comorphism -/

variable {A : Silmaril.SpecTec.Grammar.Attr α} {B : Silmaril.SpecTec.Grammar.Attr β}

@[simp] theorem fullCoHom_Φ (f : AttrHom A B) (D : Type) : (fullCoHom f D).Φ = 𝟭 _ := rfl

@[simp] theorem fullCoHom_sen (f : AttrHom A B) (D : Type) (S : Sig D) (φ : Sen S.N α) :
    ((fullCoHom f D).ρ.app S).sen φ = mapSen f φ := rfl

@[simp] theorem fullCoHom_mod_obj (f : AttrHom A B) (D : Type) (S : Sig D)
    (M : SModel f.toFun S.N) :
    ((fullCoHom f D).ρ.app S).mod.obj M = (SModel.comap f.toFun).obj M := rfl

/-- **Satisfaction transfer along `fullCoHom`**, read with `Sen.Holds`. -/
theorem fullCoHom_holds_iff (f : AttrHom A B) (D : Type) (S : Sig D) (M : SModel f.toFun S.N)
    (φ : Sen S.N α) :
    (mapSen f φ).Holds B M.1.rel ↔ φ.Holds A ((SModel.comap f.toFun).obj M).rel :=
  (fullCoHom f D).satisfaction S M φ

end Silmaril.Wasm.SpecTec.GrammarInst
