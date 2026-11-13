module

public import Silmaril.Compiler.C.Sem.Validator.Defs
@[expose] public section

/-!
# Checked realisation of C3 through Cerberus Core

The universal clause has the shape of `Targets.c2_core_realises`, using
`elabC3` and C3 (real floating types). The existence clause explicitly excludes
the always-declining stub. Scoring should additionally require an accepted
corpus program, counting each program once across the Core elaborators.

As with C0, C1 and C2, `elabC3` is worker-written: this theorem shows that C3
is faithfully realisable in Core, not that C3 matches Cerberus's own
elaboration. A bridge to Cerberus-generated Core is a separate obligation.

Acceptance is partial: an undefined source execution, unsupported syntax,
exhausted checking fuel, or differing Core behaviours must decline. In
particular, reading an uninitialised float must decline. Frozen Core uses
binary64 values and eight-byte objects for all real floating types; C3 uses
binary32/four bytes for float and binary64/eight bytes for double. Programs
observing a rounding or layout difference must therefore decline unless the
translator preserves C3's semantics explicitly. Core's float-to-integer
primitive also needs C3's destination-range checks.

The acceptance witness need not itself exercise floating arithmetic; broader
floating coverage remains an implementation and corpus-measurement goal.
No implementation or proof of this target is supplied by this statement.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.C.Sem

/-- At least one program elaborates, and every accepted program is in C3 with
exactly the behaviours of its structurally elaborated Core program. -/
def c3_core_realises : Prop :=
  (∃ (p : Silmaril.Cerberus.Ail.TypedProgram)
      (q : Silmaril.Cerberus.Core.Dynamics.Program), elabC3 p = some q) ∧
  (∀ (p : Silmaril.Cerberus.Ail.TypedProgram)
      (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC3 p = some q → C3.InFragment p ∧ Core.beh q = C3.beh p)

end Silmaril.Compile.Targets
