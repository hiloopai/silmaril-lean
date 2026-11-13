module

public import Silmaril.Compiler.C.Sem.Validator.Defs
@[expose] public section

/-!
# Checked realisation of C1 through Cerberus Core

The universal clause has the shape of `Targets.c0_core_realises`, using
`elabC1` and C1. The existence clause explicitly excludes the always-declining
stub; the evaluator should additionally gate scoring on `core1_realised`.

As with C0, `elabC1` is worker-written: this theorem shows that C1 is
faithfully realisable in Core, not that C1 matches Cerberus's own elaboration.
The bridge to Cerberus's actual Core output, comparing `elabC1` with
`cerb-oracle` Core on the corpus, is core-elab's job and a later target.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.C.Sem

/-- At least one program elaborates, and every accepted program is in C1 with
exactly the behaviours of its structurally elaborated Core program. -/
def c1_core_realises : Prop :=
  (∃ (p : Silmaril.Cerberus.Ail.TypedProgram)
      (q : Silmaril.Cerberus.Core.Dynamics.Program), elabC1 p = some q) ∧
  (∀ (p : Silmaril.Cerberus.Ail.TypedProgram)
      (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC1 p = some q → C1.InFragment p ∧ Core.beh q = C1.beh p)

end Silmaril.Compile.Targets
