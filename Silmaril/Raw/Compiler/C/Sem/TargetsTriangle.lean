module

public import Silmaril.Compiler.C.Sem.Runtime.Defs
public import Silmaril.Compiler.C.Sem.Validator.Defs
public import Silmaril.Compiler.C.Sem.C1.Defs
@[expose] public section

/-!
# The per-program triangle: ccomp's Mir factors through the elaborated Core (statements)

`Targets.triangle_factor` made concrete on real programs. When the rung-`N` validator
`checkCN` accepts a program `p` (ccomp's Mir `us` of `p`, linked with ccomp's C library, is valid
at `Core.cAM CN.sem`) and the rung-`N` Core elaboration `elabCN` answers `q` for it (`Core.beh q`
is `CN.beh p`), then ccomp's Mir factors through that Core program: `q` is a valid Ail → Core
translation of `p` and `us` a valid Core → Mir translation of `q`.

Each statement requires a program accepted by its elaborator, as well as universal
factorization. The universal clause follows from the rung's validator soundness
(`checkCN_sound`), its Core realisation (`Targets.c0_core_realises`,
`Targets.c1_core_realises`) and `C.Sem.factor`. The existence clause excludes an
always-declining elaborator. It does not mention `checkCN`: `checkCN` runs ccomp and decodes
its C library through `partial def`s, which the kernel cannot evaluate, so no concrete
acceptance `checkCN p = true` has a proof. The non-vacuity of `checkCN` is carried instead by
the evaluator's both-accept corpus gate (`tv && core` for C0, `tv1 && core1` for C1), as for
`Targets.ccomp_rt_tv_sound` and its rung variants: a statement scores only once its checker
and its elaborator both accept a corpus program. The C1 statement is false while `elabC1` is
the declining stub.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem

/-- **ccomp's Mir factors through the C0 Core elaboration**: at least one program is accepted
by `elabC0` (`checkC0`'s non-vacuity is the evaluator's corpus gate); whenever `checkC0`
accepts `p` and `elabC0` answers `q`, ccomp's Mir for `p` linked with its C library has a
behaviour and is the composite of a valid Ail → Core step to `q` and a valid Core → Mir step
from `q`. -/
def ccomp_factors_through_core_c0 : Prop :=
  (∃ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC0 p = some q) ∧
  (∀ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    checkC0 p = true → elabC0 p = some q →
      ∃ us, ccompMirRt p = some us ∧
        Valid (Core.cAC C0.sem) p q ∧ Valid (Core.cCM mirConfig ctlAddress) q us ∧
        (Mir.beh mirConfig us).Nonempty)

/-- **ccomp's Mir factors through the C1 Core elaboration**: `ccomp_factors_through_core_c0`
with `checkC1`, `elabC1` and the C1 semantics, including acceptance of at least one program by
`elabC1`. -/
def ccomp_factors_through_core_c1 : Prop :=
  (∃ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC1 p = some q) ∧
  (∀ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    checkC1 p = true → elabC1 p = some q →
      ∃ us, ccompMirRt p = some us ∧
        Valid (Core.cAC C1.sem) p q ∧ Valid (Core.cCM mirConfig ctlAddress) q us ∧
        (Mir.beh mirConfig us).Nonempty)

end Silmaril.Compile.Targets
