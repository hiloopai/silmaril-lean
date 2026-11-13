module

public import Silmaril.Compiler.C.Sem.C6.Defs
@[expose] public section

/-!
# C6 preserves C5

The extension uses the frozen C5 interpreter on its checked fragment. Equality therefore
includes undefined behaviour and divergence, without a termination or definedness premise.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.C.Sem

/-- C6 has exactly C5's behaviours on C5's fragment. -/
def c6_extends_c5 : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, C5.InFragment p → C6.beh p = C5.beh p

end Silmaril.Compile.Targets
