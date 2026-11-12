module

public import Silmaril.Wasm.SpecTec.Institution.Thms

/-!
# A facade for the institution of SpecTec specifications

`Institution.inst alts : Inst` (`Silmaril.Wasm.SpecTec.Institution`) has inclusions of signatures as
morphisms, sentences that are rules or facts in the signature, and discrete models
(`Discrete (Model S)`). This module gives the unfolding lemmas under which `simp` reads it:

* `inst_sat_iff` (`@[simp]`, `rfl`): satisfaction is `SSen.Sat alts env D` of the underlying
  sentence;
* `inst_map_sen_val` (`@[simp]`): translation along an inclusion keeps the underlying sentence;
* `inst_map_mod_obj` (`@[simp]`): the reduct is `Model.reduct`;
* `inst_entails_iff`: entailment in `inst alts` at `S` is entailment in `room alts S`.

New lemmas; the institution is unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open CategoryTheory Silmaril.Logic.Institution

/-- Satisfaction in `inst alts` is `SSen.Sat` of the underlying sentence. -/
@[simp] theorem inst_sat_iff (alts : Reading) {S : Sig} (M : Model S) (φ : Sen S) :
    ((inst alts).I.obj S).Sat (Discrete.mk M) φ ↔ φ.1.Sat alts M.env M.D := Iff.rfl

/-- Translation along an inclusion keeps the underlying sentence. -/
@[simp] theorem inst_map_sen_val (alts : Reading) {S T : Sig} (f : S ⟶ T) (φ : Sen S) :
    (((inst alts).I.map f).sen φ).1 = φ.1 := rfl

/-- The reduct of `inst alts` along an inclusion is `Model.reduct`. -/
@[simp] theorem inst_map_mod_obj (alts : Reading) {S T : Sig} (f : S ⟶ T) (M : Model T) :
    ((inst alts).I.map f).mod.obj (Discrete.mk M) = Discrete.mk (M.reduct (leOfHom f)) := rfl

/-- Entailment in `inst alts` at `S` is entailment in the room of `S`. -/
theorem inst_entails_iff (alts : Reading) (S : Sig) (Γ : Set (Sen S)) (φ : Sen S) :
    ((inst alts).I.obj S).Entails Γ φ ↔ (room alts S).Entails Γ φ := Iff.rfl

end Silmaril.Wasm.SpecTec.Institution
