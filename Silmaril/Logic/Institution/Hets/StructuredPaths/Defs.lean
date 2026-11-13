module

public import Silmaril.Logic.Institution.Hets.LogicGraph
public import Silmaril.Logic.Institution.Hets.StructuredSpec

@[expose] public section
namespace Silmaril.Logic.Institution.Hets.StructuredPaths
open CategoryTheory Silmaril.Logic.Institution
universe u₀ v₀ u v w m₁ m₂

variable (L : LogicGraph.{u₀,v₀,u,v,w,m₁,m₂}) {a b : L.Idx}

/-- The signature reached by an actual sequence of logic translations. -/
abbrev target (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign) : L.Sig :=
  IndexedCoInst.mkSig L.indexed (L.pt b)
    ((IndexedCoInst.coHom L.indexed (L.pathHom p)).Φ.obj S)

/-- The standard Hets path map in the shared flattened institution. -/
abbrev lift (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign) :
    L.sigOf a S ⟶ target L p S :=
  IndexedCoInst.lift L.indexed (L.pathHom p) S

/-- Translate any shared structured specification, including unions and hiding. -/
def translate (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat L.indexed) (L.sigOf a S)) :
    StrSpec (IndexedCoInst.flat L.indexed) (target L p S) :=
  StrSpec.translate (lift L p S) SP

/-- Hide a translated signature using the same shared structured-spec API. -/
def hide (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat L.indexed) (target L p S)) :
    StrSpec (IndexedCoInst.flat L.indexed) (L.sigOf a S) :=
  StrSpec.hide (lift L p S) SP

end Silmaril.Logic.Institution.Hets.StructuredPaths
