module

public import Silmaril.Containers.MemoryRefinement.Defs
public import Silmaril.Containers.Behaviour.Thms
public import Silmaril.Containers.Precondition.Thms
public import Silmaril.Semantics.MemoryRefinement.Thms

/-! # Container satisfaction and prefix-sensitive refinement imply WP transport -/

@[expose] public section

namespace Silmaril.Containers.MemoryRefinement

open Silmaril.Semantics.MemoryRefinement (Hom)

theorem wp_iff {Entry Event : Type} (runs : Entry → Containers.Model Event) (entry : Entry) (post : Spec Event) :
    (ofRuns runs).wp post entry ↔ (runs entry).Sat Spec.noUB ∧ (runs entry).Sat post := by
  simp [Semantics.MemoryRefinement.Model.wp, ofRuns, Containers.Model.Sat]

theorem wp_iff_vpre {Image Prog Event : Type} (runtime : Runtime Image Prog Event) (image : Image) (post : Spec Event) :
    (ofRuns runtime.beh).wp post image ↔ vpre runtime post image :=
  (wp_iff _ _ _).trans (vpre_iff runtime post image).symm

/-- `RefinesUB` even preserves the observable prefix before UB; forget that extra precision here. -/
def ofRefinesUB {A B Event : Type} {src : A → Containers.Model Event} {dst : B → Containers.Model Event}
    (rel : A → B → Prop) (sim : ∀ {a b}, rel a b → (dst b).RefinesUB (src a)) : Hom (ofRuns src) (ofRuns dst) :=
  ⟨rel, fun related safe => let noUB := Classical.not_not.mp safe
    let back := Containers.Model.refinesUB_of_noUB noUB (sim related)
    ⟨fun bad => bad (back.sat noUB), back⟩⟩

end Silmaril.Containers.MemoryRefinement
