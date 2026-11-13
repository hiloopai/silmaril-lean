module

public import Silmaril.Compiler.Category.Cerberus.Defs
public import Silmaril.Logic.Institution.Hets.LogicGraph

/-! A Hets logic graph connecting real Core semantics with compiler-category
behavioral institutions. The operational realization and the target read-back
are separate translations from the common source behavior institution. An edge
is a logic translation, not evidence of successful compiler correctness.
-/

@[expose] public section
namespace Silmaril.Compiler.Category.Cerberus.Hets

open CategoryTheory Silmaril.Logic.Institution Silmaril.Compile.Category

inductive Node where
  | coreBehaviors | coreOperational | targetBehaviors

inductive Translation : Node → Node → Type
  | realize : Translation .coreBehaviors .coreOperational
  | observe : Translation .coreBehaviors .targetBehaviors

/-- The target node is parameterized by its actual language semantics and
read-back convention. No target semantics is fabricated from driver success.
The graph does not claim model-expansiveness or borrowing of consequences in
the reverse direction. -/
def graph (target : Language.{0}) (convention : language ⟶ target)
    (readback : Convention.ReadBack convention) : LogicGraph.{0, 0, 0, 0, 0, 0, 0} where
  Logics := Node
  inst
    | .coreBehaviors => language.inst
    | .coreOperational => Core.bundled
    | .targetBehaviors => target.inst
  Comor := Translation
  comor
    | .realize => realization
    | .observe => Convention.comorphism readback
  Mor _ _ := PEmpty
  mor edge := edge.elim

/-- The actual Core realization as a path, so it participates in the existing
free-category and Grothendieck flattening machinery. -/
def realizationPath (target : Language.{0}) (convention : language ⟶ target)
    (readback : Convention.ReadBack convention) :
    Quiver.Path (show (graph target convention readback).Idx from Node.coreBehaviors)
      (show (graph target convention readback).Idx from Node.coreOperational) :=
  .cons .nil .realize

/-- The semantic observation read-back as the parallel target path. Validity
of any compiler implementation must still be established separately. -/
def observationPath (target : Language.{0}) (convention : language ⟶ target)
    (readback : Convention.ReadBack convention) :
    Quiver.Path (show (graph target convention readback).Idx from Node.coreBehaviors)
      (show (graph target convention readback).Idx from Node.targetBehaviors) :=
  .cons .nil .observe

end Silmaril.Compiler.Category.Cerberus.Hets
