module

public import Silmaril.Compiler.C.Sem.C7.Defs
@[expose] public section

/-!
# C7 preserves C6

C7 uses the C6 interpreter on C6's checked fragment. Equality therefore includes undefined
behaviour and divergence, without a termination or definedness premise.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.C.Sem

/-- C7 has exactly C6's behaviours on C6's fragment. -/
def c7_extends_c6 : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, C6.InFragment p → C7.beh p = C6.beh p

end Silmaril.Compile.Targets
