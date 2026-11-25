module

public import Silmaril.Semantics.RuntimeWires.StateWire.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.StateWire.Rules

@[expose] public section

namespace Silmaril.RuntimeWires.StateWire

open CategoryTheory Presentation
open scoped MonoidalCategory

universe u v s

variable {G : EffectfulPolygraph.{u,v}} {S : Type s}
variable (update : G.effect.Edge → S → S)

theorem run_id (X : Computations G) : run update (𝟙 X) = id :=
  (interpretation update).map_id X

/-- A shared runtime wire supplies the final state of the first computation as
the initial state of the second. -/
theorem run_comp {X Y Z : Computations G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    run update (f ≫ g) = run update g ∘ run update f :=
  (interpretation update).map_comp f g

theorem run_cast {X Y : Computations G} (p : X = Y) : run update (eqToHom p) = id := by
  cases p
  exact run_id update X

theorem run_generator (e : G.effect.Edge) : run update (effectGenerator G e) = update e :=
  Proofs.StateWire.run_gen update e

theorem run_pure {X Y : Pure G} (f : X ⟶ Y) : run update ((pureInclusion G).map f) = id :=
  Proofs.StateWire.run_pure update f

theorem run_whiskerLeft (X : Computations G) {Y Z : Computations G} (f : Y ⟶ Z) :
    run update (X ◁ f) = run update f :=
  Proofs.StateWire.run_left update X f

theorem run_whiskerRight {X Y : Computations G} (f : X ⟶ Y) (Z : Computations G) :
    run update (f ▷ Z) = run update f :=
  Proofs.StateWire.run_right update f Z

/-- A state observation separating the two orders witnesses different
computation morphisms at the same boundary. -/
theorem comp_ne_swap {X : Computations G} (f g : X ⟶ X) (s : S)
    (h : run update g (run update f s) ≠ run update f (run update g s)) :
    f ≫ g ≠ g ≫ f := by
  intro eq
  exact h (congrFun ((run_comp update f g).symm.trans
    ((congrArg (run update) eq).trans (run_comp update g f))) s)

end Silmaril.RuntimeWires.StateWire
