module

public import Silmaril.Calculi.LambdaCube.PER.CubeMorphisms
public import Silmaril.Logic.Hets.Defs

@[expose] public section

/-! # Lambda-cube restriction graphs

A node is a cube corner below a chosen top corner. Its semantics is the
restriction of one supplied semantics: all nodes retain the same raw PTS
judgments, models, and satisfaction relation. Their typing calculi differ.
Every inclusion carries an institution comorphism; the same corridor also
supplies a reverse institution morphism. These are Hets-style mathematical
graphs, with no dependency on the external Hets executable.

`PERGraph.graph` instantiates the nondependent face with the concrete
parametric PER semantics of Fω. It does not identify these restrictions with
the independent STLC set semantics or the native System F PER semantics.
-/

namespace Silmaril.Calculi.LambdaCube

open CategoryTheory Silmaril.Logic.Institution

namespace RestrictionGraph

/-- Corners whose rules are included in those of `top`. -/
abbrev Node (top : Corner) := {c : Corner // c ≤ top}

variable {top : Corner}

/-- The semantics at a node, inherited from the chosen top semantics. -/
def semantics (N : Semantics top) (c : Node top) : Semantics c.val :=
  N.restrict c.property

/-- Actual model reduct and satisfaction law along a corner inclusion. -/
def inclusion (N : Semantics top) {c d : Node top} (h : c.val ≤ d.val) :
    SemanticInclusion h (semantics N c) (semantics N d) :=
  ⟨𝟭 _, fun _ _ => Iff.rfl⟩

/-- Sentences translate toward the larger corner; models translate back. -/
def comorphism (N : Semantics top) {c d : Node top} (h : c.val ≤ d.val) :
    Inst.CoHom (semantics N c).inst (semantics N d).inst :=
  (inclusion N h).comorphism

/-- The same corridor, read as a morphism from the larger corner to the smaller. -/
def projection (N : Semantics top) {c d : Node top} (h : c.val ≤ d.val) :
    Inst.Hom (semantics N d).inst (semantics N c).inst where
  Φ := 𝟭 _
  η := Discrete.natTrans (fun _ => (inclusion N h).corridor)

/-- The downward face of the cube as a graph of proved institution maps.

The graph contains every comparable pair, including identities and diagonal
inclusions. All semantic data are inherited from `N`; this construction alone
does not construct independent semantics for the other corners. -/
def graph (N : Semantics top) : LogicGraph.{0, 0, 0, 0, 0, 1, 1} where
  Logics := Node top
  inst c := (semantics N c).inst
  Comor c d := PLift (c.val ≤ d.val)
  comor e := comorphism N e.down
  Mor c d := PLift (d.val ≤ c.val)
  mor e := projection N e.down

end RestrictionGraph

namespace PERGraph

open PERModel.SystemFOmega

/-- The four nondependent cube corners, all using Fω parametric PER semantics. -/
abbrev Node := RestrictionGraph.Node Corner.systemFOmega

/-- The simply typed corner with the restricted Fω semantics. -/
def stlc : Node := ⟨Corner.stlc, stlc_le_systemFOmega⟩

/-- The polymorphic corner with the restricted Fω semantics. -/
def systemF : Node := ⟨Corner.systemF, systemF_le_systemFOmega⟩

/-- The type-constructor corner without polymorphism or term dependency. -/
def omega : Node := ⟨Corner.omega, omega_le_systemFOmega⟩

/-- The Fω corner itself. -/
def systemFOmega : Node := ⟨Corner.systemFOmega, le_refl _⟩

/-- A concrete Hets-style logic graph, with no supplied soundness certificates. -/
def graph := RestrictionGraph.graph paramSemantics

/-- The polymorphism edge from the simply typed corner. -/
def stlcToSystemF : graph.Comor stlc systemF := ⟨Corner.stlc_le_systemF⟩

/-- The type-constructor edge from the simply typed corner. -/
def stlcToOmega : graph.Comor stlc omega :=
  ⟨by
    change Corner.stlc ≤ Corner.omega
    exact ⟨by simp [Corner.stlc], by simp [Corner.stlc], by simp [Corner.stlc]⟩⟩

/-- Add type constructors to the polymorphic corner. -/
def systemFToSystemFOmega : graph.Comor systemF systemFOmega :=
  ⟨systemF_le_systemFOmega⟩

/-- Add polymorphism to the type-constructor corner. -/
def omegaToSystemFOmega : graph.Comor omega systemFOmega :=
  ⟨omega_le_systemFOmega⟩

/-- The path through System F, as an actual path in the comorphism graph. -/
def viaSystemF : @Quiver.Path graph.Idx (LogicGraph.instQuiverIdx graph) stlc systemFOmega :=
  @Quiver.Path.cons graph.Idx (LogicGraph.instQuiverIdx graph) stlc systemF systemFOmega
    (@Quiver.Path.cons graph.Idx (LogicGraph.instQuiverIdx graph) stlc stlc systemF
      .nil stlcToSystemF) systemFToSystemFOmega

/-- The path through the constructor-only corner. -/
def viaOmega : @Quiver.Path graph.Idx (LogicGraph.instQuiverIdx graph) stlc systemFOmega :=
  @Quiver.Path.cons graph.Idx (LogicGraph.instQuiverIdx graph) stlc omega systemFOmega
    (@Quiver.Path.cons graph.Idx (LogicGraph.instQuiverIdx graph) stlc stlc omega
      .nil stlcToOmega) omegaToSystemFOmega

end PERGraph

end Silmaril.Calculi.LambdaCube
