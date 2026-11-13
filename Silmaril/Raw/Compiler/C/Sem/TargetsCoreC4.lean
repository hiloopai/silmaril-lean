module

public import Silmaril.Compiler.C.Sem.Validator.Defs
@[expose] public section

/-!
# Checked realisation of C4 through Cerberus Core

The universal clause has the shape of `Targets.c3_core_realises`, using
`elabC4` and C4 (function pointers and typed variadic calls). The existence
clause explicitly excludes the always-declining stub. Scoring should additionally
require an accepted corpus program, counting each program once across the Core
elaborators.

As with C0 through C3, `elabC4` is worker-written: this theorem shows that C4
is faithfully realisable in Core, not that C4 matches Cerberus's own
elaboration. A bridge to Cerberus-generated Core is a separate obligation.

Acceptance is partial: an undefined source execution, unsupported syntax,
exhausted checking fuel, or differing Core behaviours must decline. Frozen Core
supports symbolic function pointers, equality and indirect procedure calls.
C4's integer code tokens are not Core's symbolic pointers: programs observing
their representation must decline unless the translator preserves the observation.
Core's procedure arguments have fixed arity; its variadic metadata does not
implement `va_start`, `va_arg`, `va_copy` or `va_end`. These operations must
initially decline; accepting them needs an explicit encoding preserving C4's
promoted argument types, shared cursors, copies and activation lifetimes, or a
separately approved change to Core. C3's floating rounding and layout limits,
and the current structural elaborator's unsupported syntax, also remain relevant.

The acceptance witness need not itself exercise a function pointer or variadic
call; broader coverage remains an implementation and corpus-measurement goal.
No implementation or proof of this target is supplied by this statement.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.C.Sem

/-- At least one program elaborates, and every accepted program is in C4 with
exactly the behaviours of its structurally elaborated Core program. -/
def c4_core_realises : Prop :=
  (∃ (p : Silmaril.Cerberus.Ail.TypedProgram)
      (q : Silmaril.Cerberus.Core.Dynamics.Program), elabC4 p = some q) ∧
  (∀ (p : Silmaril.Cerberus.Ail.TypedProgram)
      (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC4 p = some q → C4.InFragment p ∧ Core.beh q = C4.beh p)

end Silmaril.Compile.Targets
