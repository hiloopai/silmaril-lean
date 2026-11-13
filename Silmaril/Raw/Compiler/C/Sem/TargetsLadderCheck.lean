module

public import Silmaril.Compiler.C.Sem.LadderCheck.Defs
@[expose] public section

/-!
# Proposed targets for checked adjacent-rung agreement

Each target combines an acceptance witness with universal soundness. The first
clause excludes an always-false checker; the second gives exact equality of the
unbounded behaviour sets for every accepted program, without a fragment or
definedness premise. The checker itself declines UB and incomplete executions.

These are statements only, pending coordinator acceptance before target proofs.
They neither assert nor depend on any universal ladder law in `TargetsLadder`.
The existing C6/C5 equality target is unchanged.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.C.Sem
open Silmaril.Cerberus.Ail

/-- The C0/C1 check accepts some program and guarantees exact behaviour equality. -/
def ladder_check_sound_c1 : Prop :=
  (∃ p : TypedProgram, ladderCheck1 p = true) ∧
  ∀ p : TypedProgram, ladderCheck1 p = true → C1.beh p = C0.beh p

/-- The C1/C2 check accepts some program and guarantees exact behaviour equality. -/
def ladder_check_sound_c2 : Prop :=
  (∃ p : TypedProgram, ladderCheck2 p = true) ∧
  ∀ p : TypedProgram, ladderCheck2 p = true → C2.beh p = C1.beh p

/-- The C3/C4 check accepts some program and guarantees exact behaviour equality. -/
def ladder_check_sound_c4 : Prop :=
  (∃ p : TypedProgram, ladderCheck4 p = true) ∧
  ∀ p : TypedProgram, ladderCheck4 p = true → C4.beh p = C3.beh p

/-- The C4/C5 check accepts some program and guarantees exact behaviour equality. -/
def ladder_check_sound_c5 : Prop :=
  (∃ p : TypedProgram, ladderCheck5 p = true) ∧
  ∀ p : TypedProgram, ladderCheck5 p = true → C5.beh p = C4.beh p

end Silmaril.Compile.Targets
