module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.SelectedSoundness.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Determinism.Defs
public import Silmaril.Compile.Category.Pass
public import Silmaril.Compiler.Category.Institution.Defs
public import Silmaril.Logic.Institution.Hets.LogicGraph

/-! A behavioural institution for actual finite successful pure open-Mir blocks.
The context fixes the real partial input frame and memory. The program domain
requires an actual successful execution, independently of optimization. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.Institution
open Silmaril.Machine Silmaril.Compile

/-- A real open-block execution context. No register or slot is completed. -/
structure Context where
  calls : OpenCalls
  base : Nat
  frame : Lir.Frame Nat
  memory : Lir.Memory

/-- The actual source relation has at least one finite successful execution.
Missing input reads and other executions outside this domain are not covered. -/
def Defined (context : Context) (block : Mir.Block) : Prop :=
  ∃ exit final memory, BlockExec context.calls block context.frame context.memory exit final memory

/-- The domain is independent of optimizer selection or a behavior witness. -/
def Program (context : Context) :=
  { block : Mir.Block // Validation.Lists.Admitted block.instrs.toList ∧ Defined context block }

/-- Complete boundary observations: exit, memory, every partial low-register
read and the entire partial slot function. Fresh high registers are internal. -/
structure Observation (base : Nat) where
  exit : BlockExit
  memory : Lir.Memory
  registers : Fin base → Option Lir.Word
  slots : Nat → Option Lir.Word

/-- Project an actual completed execution frame without completing missing reads. -/
def observe (base : Nat) (exit : BlockExit) (frame : Lir.Frame Nat) (memory : Lir.Memory) :
    Observation base :=
  ⟨exit, memory, fun reg => frame.get reg.val, frame.slots⟩

/-- All actual executions contribute behaviors; no chosen existence witness is
used to define the model. -/
def behaviors (context : Context) (block : Mir.Block) : Set (Observation context.base) :=
  { observation | ∃ exit final memory,
    BlockExec context.calls block context.frame context.memory exit final memory ∧
    observe context.base exit final memory = observation }

/-- One context gives one concrete language, with the sole interface describing
this fixed open-block boundary. Program behaviors remain actual executions. -/
def language (context : Context) : Category.Language where
  Iface := Unit
  Prog := Program context
  iface := fun _ => ()
  Obs := Observation context.base
  beh := fun program => behaviors context program.val

/-- The existing behavioral-institution construction applied to this real
finite-block language. -/
def institution (context : Context) := (language context).inst

namespace Hets
open CategoryTheory Silmaril.Logic.Institution

inductive Node where
  | source | optimized

inductive Translation : Node → Node → Type
  | optimize : Translation .source .optimized

/-- Both nodes retain the real finite-block execution institution. The edge
uses the optimizer's identity observation convention; actual program model
preservation is proved separately from actual successful pass execution. -/
def graph (context : Context) : LogicGraph.{0, 0, 0, 0, 0, 0, 0} where
  Logics := Node
  inst _ := institution context
  Comor := Translation
  comor
    | .optimize => Category.Convention.comorphism (Category.Convention.ReadBack.id (language context))
  Mor _ _ := PEmpty
  mor edge := edge.elim

/-- The real local optimizer edge participates in the existing Hets free
category and Grothendieck institution machinery. -/
def optimizerPath (context : Context) :
    Quiver.Path (show (graph context).Idx from Node.source)
      (show (graph context).Idx from Node.optimized) :=
  .cons .nil .optimize

end Hets

end Silmaril.Compiler.Native.Optimize.LambdaSSA.Institution
