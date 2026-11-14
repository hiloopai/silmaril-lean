module

public import Silmaril.Automata.Institution.Defs
import Silmaril.Proofs.Automata.Institution

@[expose] public section

/-!
# The machine institution: theorems and the institution

PROVED (standard axioms; proofs in `Silmaril/Proofs/Automata/Institution.lean`):

* `sat_map_iff`: **the satisfaction condition** `M ⊨ σ(φ) ↔ M|σ ⊨ φ` for every signature
  morphism `σ`, model `M` and sentence `φ`;
* `Sen.map_id`, `Sen.map_comp`: sentence translation is functorial;
* so `inst : Sig ⥤ Room` is an institution, and `classic` its direct (Goguen–Burstall) form;
* `sat_toSpec_iff`: **typed and JSON machines satisfy the same problems**: a typed machine
  satisfies `φ` iff the model of its JSON spec (names as states) satisfies `φ` renamed to
  names.
-/

namespace Silmaril.Automata.Inst

open CategoryTheory Silmaril.Logic.Institution

theorem sat_map_iff {A B : Sig} (σ : A ⟶ B) (M : Model B) (φ : Sen A) :
    Sat M (φ.map σ) ↔ Sat (M.reduct σ) φ :=
  Silmaril.Proofs.Automata.sat_map_iff σ M φ

theorem Sen.map_id {A : Sig} (φ : Sen A) : φ.map (𝟙 A) = φ := Silmaril.Proofs.Automata.map_id φ

theorem Sen.map_comp {A B C : Sig} (σ : A ⟶ B) (τ : B ⟶ C) (φ : Sen A) :
    φ.map (σ ≫ τ) = (φ.map σ).map τ :=
  Silmaril.Proofs.Automata.map_comp σ τ φ

/-- The room of a signature: problems, machines (discrete), satisfaction. -/
def room (A : Sig) : Room.{0, 1, 1} :=
  ⟨Sen A, Cat.of (Discrete (Model A)), fun M φ => Sat (Discrete.as M) φ⟩

/-- The corridor of a signature morphism. -/
def corridor {A B : Sig} (σ : A ⟶ B) : room A ⟶ room B :=
  ⟨Sen.map σ, Discrete.functor fun (M : Model B) => Discrete.mk (M.reduct σ),
    fun M φ => sat_map_iff σ (Discrete.as M) φ⟩

/-- **The machine institution**, as a functor into rooms. -/
def inst : Sig ⥤ Room.{0, 1, 1} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext fun φ => Sen.map_id φ)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))
  map_comp σ τ := Room.hom_ext (funext fun φ => Sen.map_comp σ τ φ)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))

/-- The machine institution in the direct form. -/
def classic : ClassicInstitution.{1, 0, 0, 1, 1} Sig := ClassicInstitution.ofRoomFunctor inst

theorem sat_toSpec_iff {S L : Type} [FinNamed S] [FinNamed L] (M : DMachine S L)
    (φ : Sen (sigOf S L)) :
    Sat (DMachine.model M) φ ↔ Sat (specModel M.toSpec) (φ.map (nameHom S L)) :=
  Silmaril.Proofs.Automata.sat_toSpec_iff M φ

end Silmaril.Automata.Inst
