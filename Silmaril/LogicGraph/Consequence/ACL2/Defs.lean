module

public import Silmaril.Logic.ACL2.Consequence.Thms
public import Silmaril.Logic.Consequence.Institution.Thms
public import Silmaril.LogicGraph.Nodes.Logic.Defs
public import Silmaril.Project.Shapes.Consequence.Defs

/-! # ACL2 fragment consequence at the example book's output signature -/

@[expose] public section

namespace Silmaril.LogicGraph.Consequence

open Silmaril.Consequence Silmaril.Logic Silmaril.Project.Shapes.Consequence

def acl2Derives := LogicalSystem.listSys ACL2.logic ACL2.Examples.exampleWorld.signature
def acl2Entails := roomSeq (ACL2.room ACL2.Examples.exampleWorld.signature)

silmaril consequence_system logic.consequence.acl2.derives := acl2Derives
  (room := "logic.acl2.room")
  (room_at := "Silmaril.Logic.ACL2.Examples.exampleWorld.signature")
  (reading := "derivability") (title := "ACL2 fragment: derivability over the arity signature")
  (doc := "SILMARIL-FIRST is declared at arity one. Derivations use the fragment rules and the supplied premises.")
silmaril consequence_system logic.consequence.acl2.entails := acl2Entails
  (room := "logic.acl2.room")
  (room_at := "Silmaril.Logic.ACL2.Examples.exampleWorld.signature")
  (reading := "semantic") (title := "ACL2 fragment: consequence over the arity signature")
  (doc := "SILMARIL-FIRST is interpreted by an arbitrary total unary function.")
silmaril consequence_system logic.consequence.acl2.presented.derives := ACL2.Consequence.exampleDerives
  (room := "logic.acl2.presented_room")
  (room_at := "Silmaril.Logic.ACL2.Examples.exampleWorld.presentation")
  (reading := "derivability") (title := "ACL2 fragment: derivability with the example definition")
  (doc := "Derivations use the fragment rules, the defining equation of SILMARIL-FIRST and the supplied premises.")
silmaril consequence_system logic.consequence.acl2.presented.entails := ACL2.Consequence.exampleEntails
  (room := "logic.acl2.presented_room")
  (room_at := "Silmaril.Logic.ACL2.Examples.exampleWorld.presentation")
  (reading := "semantic") (title := "ACL2 fragment: consequence with the example definition")
  (doc := "Models satisfy the defining equation of SILMARIL-FIRST.")

silmaril instance logic.consequence.acl2.sound (expect := THM)
  (title := "ACL2 fragment derivability is sound over the arity signature") :=
  silmaril.shapes.consequence.sound_at (S := acl2Derives) (T := acl2Entails)
@[answers "logic.consequence.acl2.sound" thm]
theorem acl2_sound : ∀ Γ φ, SoundAt acl2Derives acl2Entails Γ φ :=
  listSys_le_roomSeq ACL2.logic_sound _

silmaril instance logic.consequence.acl2.presented.sound (expect := THM)
  (title := "ACL2 fragment derivability is sound with the example definition") :=
  silmaril.shapes.consequence.sound_at
    (S := ACL2.Consequence.exampleDerives) (T := ACL2.Consequence.exampleEntails)
@[answers "logic.consequence.acl2.presented.sound" thm]
theorem acl2_presented_sound :
    ∀ Γ φ, SoundAt ACL2.Consequence.exampleDerives ACL2.Consequence.exampleEntails Γ φ :=
  ACL2.Consequence.exampleSound

silmaril instance logic.consequence.acl2.presented.first_singleton (expect := THM)
  (title := "Applying SILMARIL-FIRST to a singleton returns its element") :=
  silmaril.shapes.consequence.derives (S := ACL2.Consequence.exampleDerives) (Γ := [])
    (φ := ACL2.Examples.firstSingleton)
@[answers "logic.consequence.acl2.presented.first_singleton" thm]
theorem acl2_first_singleton : ACL2.Consequence.exampleDerives [] ACL2.Examples.firstSingleton :=
  let proof : ACL2.Examples.exampleWorld.Provable ACL2.Examples.firstSingleton :=
    .hyp (Or.inr ⟨ACL2.Examples.firstSingletonName, rfl⟩)
  (ACL2.Examples.exampleWorld_checked.pi_derives proof).weaken
    (Set.union_subset_union_right _ (Set.empty_subset _))

end Silmaril.LogicGraph.Consequence
