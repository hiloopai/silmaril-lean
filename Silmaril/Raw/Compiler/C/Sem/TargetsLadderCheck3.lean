module

public import Silmaril.Compiler.C.Sem.LadderCheck3.Defs
@[expose] public section

/-!
# Proposed target for checked C2/C3 agreement

The acceptance witness excludes an always-false checker. Universal soundness
requires equality of the full behaviour sets on every accepted program, without
a fragment or definedness premise. This statement does not assert the false
universal C2/C3 ladder law. It awaits coordinator acceptance before proof.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.C.Sem
open Silmaril.Cerberus.Ail

/-- The C2/C3 check accepts some program and guarantees exact behaviour equality. -/
def ladder_check_sound_c3 : Prop :=
  (∃ p : TypedProgram, ladderCheck3 p = true) ∧
  ∀ p : TypedProgram, ladderCheck3 p = true → C3.beh p = C2.beh p

end Silmaril.Compile.Targets
