module

public import Silmaril.Compiler.C.Sem.Validator.Defs
@[expose] public section

/-!
# Checked realisation of C2 through Cerberus Core

The universal clause has the shape of `Targets.c1_core_realises`, using
`elabC2` and C2 (structs and unions). The existence clause explicitly excludes
the always-declining stub. Scoring should additionally require an accepted
corpus program, counting each program once across the Core elaborators.

As with C0 and C1, `elabC2` is worker-written: this theorem shows that C2 is
faithfully realisable in Core, not that C2 matches Cerberus's own elaboration.
The bridge to Cerberus's actual Core output, comparing `elabC2` with
`cerb-oracle` Core on the corpus, is core-elab's job and a later target.

Acceptance is partial: an undefined source execution, unsupported syntax,
exhausted checking fuel, or differing Core behaviours must decline. In
particular, reading an uninitialised struct member must decline, as must a
program observing a pointer address when the C2 and Core layouts disagree.
The acceptance witness need not itself exercise a struct or union; broader
aggregate coverage remains an implementation and corpus-measurement goal.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.C.Sem

/-- At least one program elaborates, and every accepted program is in C2 with
exactly the behaviours of its structurally elaborated Core program. -/
def c2_core_realises : Prop :=
  (∃ (p : Silmaril.Cerberus.Ail.TypedProgram)
      (q : Silmaril.Cerberus.Core.Dynamics.Program), elabC2 p = some q) ∧
  (∀ (p : Silmaril.Cerberus.Ail.TypedProgram)
      (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC2 p = some q → C2.InFragment p ∧ Core.beh q = C2.beh p)

end Silmaril.Compile.Targets
