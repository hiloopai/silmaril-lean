module

public import Silmaril.Cerberus.Core.Forced.Defs
public import Silmaril.Compiler.Core.Verified.ReturnLit.Defs

/-! Boundary and memory contracts for returning a recognized literal from an
actual Core callee. No caller continuation or whole-program behavior is assumed. -/
@[expose] public section
namespace Silmaril.Compiler.Core.CalleeReturn
open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified

/-- The pure literal callee can change diagnostic location only. -/
def LocationOnly (before after : Mem.Concrete.State) : Prop :=
  ∃ location, after = {before with currentLocation := location}

/-- Frames local to the callee stop at its boundary; the caller may itself
contain any number of procedure or initializer boundaries. -/
def ReturnsTo (ownLabels : Labels) (callerFrames frames : List Frame) : Prop :=
  ∃ localFrames, ReturnLit.NoBoundary localFrames ∧
    frames = localFrames ++ .procedureReturn ownLabels :: callerFrames

end Silmaril.Compiler.Core.CalleeReturn
