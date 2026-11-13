module

public import Silmaril.Compiler.Native.Correctness.Institution.Defs
public import Silmaril.Compiler.Category.Cerberus.Hets.Defs
/-! The native projected compiler institutions and the full Core operational
institution share one Hets logic graph. Its projection and realization edges
have proved satisfaction conditions. No edge proves native code correctness or
transports arbitrary full-state properties through the process projection. -/

@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.Hets

open CategoryTheory Silmaril.Logic.Institution Silmaril.Compile.Category

inductive Node where
  | coreBehaviors | coreOperational | projectedCore | nativeMachine

inductive Translation : Node → Node → Type
  | realize : Translation .coreBehaviors .coreOperational
  | project : Translation .projectedCore .coreOperational
  | compile : Translation .projectedCore .nativeMachine

def graph (domain : Source → Prop) (toolchain : Toolchain domain) : LogicGraph.{0, 0, 0, 0, 0, 0, 0} where
  Logics := Node
  inst
    | .coreBehaviors => Silmaril.Compiler.Category.Cerberus.language.inst
    | .coreOperational => Silmaril.Cerberus.Institution.bundled
    | .projectedCore => (sourceLanguage domain).inst
    | .nativeMachine => (targetLanguage toolchain).inst
  Comor := Translation
  comor
    | .realize => Silmaril.Compiler.Category.Cerberus.realization
    | .project => Institution.projection domain
    | .compile => Institution.native domain toolchain
  Mor _ _ := PEmpty
  mor edge := edge.elim

def projectionPath (domain : Source → Prop) (toolchain : Toolchain domain) :
    Quiver.Path (show (graph domain toolchain).Idx from Node.projectedCore)
      (show (graph domain toolchain).Idx from Node.coreOperational) :=
  .cons .nil .project

def nativePath (domain : Source → Prop) (toolchain : Toolchain domain) :
    Quiver.Path (show (graph domain toolchain).Idx from Node.projectedCore)
      (show (graph domain toolchain).Idx from Node.nativeMachine) :=
  .cons .nil .compile

end Silmaril.Compiler.Native.Correctness.Hets
