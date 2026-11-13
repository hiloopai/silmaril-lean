module

public import Silmaril.Compiler.C.Sem.Runtime.Defs
public import Silmaril.Compiler.C.Sem.Validator.Defs
public import Silmaril.Compiler.C.Sem.C1.Defs
@[expose] public section

/-!
# The validator target for the C1 rung (frozen)

`Targets.ccomp_rt_tv_sound` (`TargetsRt.lean`) with `checkC0` replaced by `checkC1` and the
C0 semantics by the C1 semantics (`C1.lean`, flat byte memory): ccomp's Mir of the program,
linked with ccomp's C library (`ccompMirRt`, `Runtime.lean`), is valid at the read-back
convention for C1. It is scored with the number of programs `checkC1` accepts.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem

/-- **The Ail → Mir validator for C1 is sound over ccomp's pipeline with its C library**
(goal 1, by translation validation, on the C1 rung): whenever `checkC1` accepts a program,
ccomp's Mir for it, linked with ccomp's C library, is valid at the read-back convention for C1
and has a behaviour. -/
def ccomp_rt_tv_sound_c1 : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, checkC1 p = true →
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C1.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty

end Silmaril.Compile.Targets
