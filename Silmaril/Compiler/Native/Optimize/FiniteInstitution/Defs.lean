module

public import Silmaril.Compiler.Native.Optimize.Validation.Finite.Defs
public import Silmaril.Compiler.Mir.Pass.Defs
public import Silmaril.Compile.Category.Pass
public import Silmaril.Compiler.Category.Institution.Defs
public import Silmaril.Logic.Institution.Hets.LogicGraph

/-! The actual native optimizer on an independently defined finite-success
program domain, retaining every actual MirSem behavior in the model. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.FiniteInstitution
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract

/-- The real program-start context. Symbol placement and memory size stay fixed. -/
structure Context where
  calls : OpenCalls
  placement : MirSem.Placement
  size : Nat

/-- Independent finite successful actual startup and execution of an admitted
entry function. This predicate does not refer to any compiler or checker. -/
def Defined (context : Context) (units : Array Mir.Unit) : Prop :=
  ∃ function frame outcome,
    Validation.Finite.AdmittedFunction function ∧
    MirSem.start units context.placement context.size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units context.placement context.size⟩ ∧
    MirSem.Behaves units context.placement
      ⟨function, 0, 0, frame, [], MirSem.initMem units context.placement context.size⟩
      (Validation.Finite.Outcome.behavior outcome)

/-- Proof fields restrict the semantic domain; the runtime program is real Mir units. -/
def Program (context : Context) := { units : Array Mir.Unit // Defined context units }

/-- All actual behaviors from actual startup, including the stuck and divergent
cases of the existing relation. No existence witness defines this model. -/
def behaviors (context : Context) (units : Array Mir.Unit) : Set Lir.Behavior :=
  { behavior | ∃ state, MirSem.start units context.placement context.size = some state ∧
      MirSem.Behaves units context.placement state behavior }

/-- The exact supported configuration of the existing compiler: cleanup passes
are disabled; localSSA and lambdaSSA retain their actual independent flags. -/
structure NoCleanup (cfg : Config) : Prop where
  constantPropagation : cfg.constantPropagation = false
  commonSubexpressions : cfg.commonSubexpressions = false
  deadCode : cfg.deadCode = false
  jumpThreading : cfg.jumpThreading = false

def language (context : Context) : Category.Language where
  Iface := Unit
  Prog := Program context
  iface := fun _ => ()
  Obs := Lir.Behavior
  beh := fun program => behaviors context program.val

/-- The existing behavioral institution on complete real machine behavior sets. -/
def institution (context : Context) := (language context).inst

namespace Hets
open CategoryTheory Silmaril.Logic.Institution

inductive Node where
  | source | optimized

inductive Translation : Node → Node → Type
  | optimize : Translation .source .optimized

/-- The identity observation edge; its connection to the actual
compiler programs is established by execution-based model equality. -/
def graph (context : Context) : LogicGraph.{0, 0, 0, 0, 0, 0, 0} where
  Logics := Node
  inst _ := institution context
  Comor := Translation
  comor
    | .optimize => Category.Convention.comorphism (Category.Convention.ReadBack.id (language context))
  Mor _ _ := PEmpty
  mor edge := edge.elim

def optimizerPath (context : Context) :
    Quiver.Path (show (graph context).Idx from Node.source)
      (show (graph context).Idx from Node.optimized) :=
  .cons .nil .optimize

end Hets
end Silmaril.Compiler.Native.Optimize.FiniteInstitution
