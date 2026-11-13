module

public import Silmaril.Compiler.Native.Correctness.AdditionMain.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionOpenFrame.Defs
public import Silmaril.Compile.Category.Pass
public import Silmaril.Compiler.Category.Institution.Defs
public import Silmaril.Logic.Institution.Hets.LogicGraph

/-! Actual unoptimized lowering from independently bounded addition to an
independent native Artifact domain at an explicit open-frame process boundary.
No source adequacy, successful compilation or target execution is assumed. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionInstitution

open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Semantics

abbrev Observation := Silmaril.Compile.Core.Spec.Obs

/-- Mathematical input domain selected before elaboration or compilation. -/
structure Program where
  left : Int
  right : Int
  bounds : AdditionSource.Bounds left right

/-- The actual fixed Cerberus source process, including its UB alternative. -/
def sourceBehaviors (program : Program) : Set Observation := {observation |
  Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreUB
      (AdditionMain.sourceDocument program.left program.right)
      (AdditionSource.source program.left program.right).arguments ∨
    Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreBeh
      (AdditionMain.sourceDocument program.left program.right)
      (AdditionSource.source program.left program.right).arguments observation}

/-- Explicit compile tag and unimplemented runtime/target/frame boundary.
This is independent of the source input and of every successful compilation. -/
structure Context where
  tag : String
  environment : OpenFrame.Environment
  memory : Lir.Memory

/-- Independent actual Artifact invocation domain. It has no source bounds,
syntactic admission, finite-execution or compiler-image predicate. -/
structure Target where
  artifact : Artifact
  name : String
  arguments : List Lir.Word

/-- Fixed no-output closed-main process projection. Malformed return shapes,
traps and stuckness remain faults; divergence remains observable. -/
def observe : Lir.Behavior → Observation
  | .returned [value] _ => .exit (value.toNat % 256) []
  | .returned _ _ | .trapped _ | .stuck => .fault []
  | .diverges => .diverges

/-- All actual open-frame observations, projected only after execution. -/
def targetBehaviors (context : Context) (target : Target) : Set Observation := {observation |
  ∃ behavior, OpenFrame.Observes target.artifact context.environment target.name
    target.arguments context.memory behavior ∧ observe behavior = observation}

def sourceLanguage : Category.Language where
  Iface := Unit
  Prog := Program
  iface _ := ()
  Obs := Observation
  beh := sourceBehaviors

def targetLanguage (context : Context) : Category.Language where
  Iface := Unit
  Prog := Target
  iface _ := ()
  Obs := Observation
  beh := targetBehaviors context

def sourceInstitution := sourceLanguage.inst
def targetInstitution (context : Context) := (targetLanguage context).inst

def convention (context : Context) : Category.Convention sourceLanguage (targetLanguage context) :=
  ⟨fun _ => (), (· = ·)⟩

def readBack (context : Context) : Category.Convention.ReadBack (convention context) :=
  ⟨_root_.id, fun _ _ => Iff.rfl⟩

/-- The exact existing unoptimized lowerer; its errors are retained.
No checker, guard, optimizer, fallback or successful-output assumption is added. -/
def run (context : Context) (program : Program) : Option Target :=
  match Lower.compile context.tag (AdditionSource.program program.left program.right) with
  | .ok artifact => some ⟨artifact, "main", []⟩
  | .error _ => none

/-- Independently stated output, identified with `run` by a theorem. -/
def expected (program : Program) : Target :=
  ⟨AdditionLower.artifact (BitVec.ofInt 64 program.left) (BitVec.ofInt 64 program.right), "main", []⟩

namespace Hets
open CategoryTheory Silmaril.Logic.Institution

inductive Node where
  | cerberus | openNative

inductive Translation : Node → Node → Type
  | lower : Translation .cerberus .openNative

def graph (context : Context) : LogicGraph.{0, 0, 0, 0, 0, 0, 0} where
  Logics := Node
  inst
    | .cerberus => sourceInstitution
    | .openNative => targetInstitution context
  Comor := Translation
  comor
    | .lower => Category.Convention.comorphism (readBack context)
  Mor _ _ := PEmpty
  mor edge := edge.elim

def loweringPath (context : Context) :
    Quiver.Path (show (graph context).Idx from Node.cerberus)
      (show (graph context).Idx from Node.openNative) :=
  .cons .nil .lower

end Hets
end Silmaril.Compiler.Native.Correctness.AdditionInstitution
