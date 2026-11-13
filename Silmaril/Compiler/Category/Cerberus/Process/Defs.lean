module

public import Silmaril.Compiler.Category.Cerberus.Defs
public import Silmaril.Compiler.Core.Spec.Defs

/-! Exact process observations of actual Core institution behaviors. This layer
uses the imported compiler specification, but no elaborator or compiler success
premise. Arbitrary finite prefixes remain institution behaviors; only terminal
states have process observations.
-/

@[expose] public section
namespace Silmaril.Compiler.Category.Cerberus.Process

open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics

namespace Spec
export Silmaril.Compile.Core.Spec (Obs coreStart coreStep CoreReach CoreUB CoreBeh
  exitStatuses coreBytes)
end Spec

/-- The actual Core model of a document at a selected startup configuration.
The corresponding successful startup equation is an explicit theorem premise.
-/
def model (document : Codec.Document) (initial : State) (labels : Labels) : Core.Model :=
  ⟨document.file, labels, initial⟩

/-- Fixed process observation of an actual labeled Core behavior. Finite
prefixes ending before termination do not produce a completed process result.
There are no defined Core process observations for faults, traps or exhaustion.
This relation retains the imported specification's treatment of unspecified
integer return values and its exact stdout encoding.
-/
def Observes : Core.Behavior → Spec.Obs → Prop
  | .finite _ state, .exit status stdout =>
      ∃ value, state.control = .halt (.defined value) ∧
        Spec.exitStatuses value status ∧ Spec.coreBytes state.memory.stdout = stdout
  | .finite _ state, .abort stdout =>
      state.control = .halt .aborted ∧ Spec.coreBytes state.memory.stdout = stdout
  | .infinite _ _, .diverges => True
  | _, _ => False

end Silmaril.Compiler.Category.Cerberus.Process
