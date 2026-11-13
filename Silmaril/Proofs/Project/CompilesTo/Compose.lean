module

public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Compiler.CompilesTo.Sim.Thms

/-!
# A C function closed from its segments

`FnData.whole_of_segments`: the composition theorem `Corr.whole_of_segments` for the
correspondence of a C function and its machine code.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.CompilesTo

namespace FnData

/-- **A function closed from its segments**: if every segment of the function's correspondence
is simulated on `I`, the function compiles to its code on `I`. -/
theorem whole_of_segments (F : FnData) (I : Model) (h : ∀ k, F.Segment I k) : F.Whole I :=
  fun k0 => (F.corr I k0).whole_of_segments (fun k => h k k0) 0

end FnData

end Silmaril.Project.CompilesTo

end
