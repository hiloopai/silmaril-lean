module

public import Silmaril.Cerberus.Core.Administrative.Thms

@[expose] public section
namespace Silmaril.Cerberus.Core.Administrative
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

/-- Structural scheduling predicates of an internal continuation. No execution
or successful result is part of this condition. -/
def PlainFrames (frames : List Frame) : Prop :=
  controlHasCCall (.value .unit) frames = false ∧ activeCall (.value .unit) frames = false

end Silmaril.Cerberus.Core.Administrative
