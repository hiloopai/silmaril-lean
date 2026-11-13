module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Finite.Thms
public import Silmaril.Compiler.Native.Optimize.FiniteInstitution.Defs
public import Silmaril.Compile.Category.Pass
public import Silmaril.Compiler.Category.Institution.Defs
public import Silmaril.Logic.Institution.Hets.LogicGraph

/-! Actual configured/default native compilation from ordinary-address-admitted finite
source programs to independently finite target programs. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.AddressInstitution
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract

/-- Reuse the actual fixed startup context; this does not reuse the older
finite institution's syntax/domain or cleanup restrictions. Its legacy calls
field is unused: the actual address layer always derives real unit/placement
resolution from the concrete finite theorem. -/
abbrev Context := FiniteInstitution.Context

/-- Actual source startup and finite execution, with independently admitted
ordinary-address entry blocks. No compiler or selected candidate occurs here. -/
def SourceDefined (context : Context) (units : Array Mir.Unit) : Prop :=
  ∃ function frame outcome,
    Validation.Address.Effects.Finite.AdmittedFunction function ∧
    MirSem.start units context.placement context.size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units context.placement context.size⟩ ∧
    MirSem.Behaves units context.placement
      ⟨function, 0, 0, frame, [], MirSem.initMem units context.placement context.size⟩
      (Validation.Finite.Outcome.behavior outcome)

/-- Independent actual finite startup/behavior. No syntactic admission,
optimization relation or candidate execution contract is part of this domain. -/
def TargetDefined (context : Context) (units : Array Mir.Unit) : Prop :=
  ∃ outcome : Validation.Finite.Outcome,
    Validation.Cleanup.ProgramBehaves units context.placement context.size outcome.behavior

def SourceProgram (context : Context) := { units : Array Mir.Unit // SourceDefined context units }
def TargetProgram (context : Context) := { units : Array Mir.Unit // TargetDefined context units }

/-- Every actual raw machine behavior from actual startup, including stuckness
and divergence. Domain witnesses do not select or filter this model. -/
abbrev behaviors := FiniteInstitution.behaviors

def sourceLanguage (context : Context) : Category.Language where
  Iface := Unit
  Prog := SourceProgram context
  iface := fun _ => ()
  Obs := Lir.Behavior
  beh := fun program => behaviors context program.val

def targetLanguage (context : Context) : Category.Language where
  Iface := Unit
  Prog := TargetProgram context
  iface := fun _ => ()
  Obs := Lir.Behavior
  beh := fun program => behaviors context program.val

def sourceInstitution (context : Context) := (sourceLanguage context).inst
def targetInstitution (context : Context) := (targetLanguage context).inst

/-- Equality of complete actual observations across the distinct domains. -/
def convention (context : Context) : Category.Convention (sourceLanguage context) (targetLanguage context) :=
  ⟨fun _ => (), (· = ·)⟩

def readBack (context : Context) : Category.Convention.ReadBack (convention context) :=
  ⟨_root_.id, fun _ _ => Iff.rfl⟩

namespace Hets
open CategoryTheory Silmaril.Logic.Institution

inductive Node where
  | source | optimized

inductive Translation : Node → Node → Type
  | optimize : Translation .source .optimized

def graph (context : Context) : LogicGraph.{0, 0, 0, 0, 0, 0, 0} where
  Logics := Node
  inst
    | .source => sourceInstitution context
    | .optimized => targetInstitution context
  Comor := Translation
  comor
    | .optimize => Category.Convention.comorphism (readBack context)
  Mor _ _ := PEmpty
  mor edge := edge.elim

def optimizerPath (context : Context) :
    Quiver.Path (show (graph context).Idx from Node.source)
      (show (graph context).Idx from Node.optimized) :=
  .cons .nil .optimize

end Hets
end Silmaril.Compiler.Native.Optimize.AddressInstitution
