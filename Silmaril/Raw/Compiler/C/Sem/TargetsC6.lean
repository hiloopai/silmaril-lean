module

public import Silmaril.Compiler.C.Sem.Runtime.Defs
public import Silmaril.Compiler.C.Sem.ValidatorC6.Defs
public import Silmaril.Compiler.C.Sem.C6.Defs
@[expose] public section

/-!
# The validator target for the C6 rung

`Targets.ccomp_rt_tv_sound_c4` (`TargetsC4.lean`) with `checkC4` replaced by `checkC6` and
the C4 semantics by the C6 semantics (`C6.lean`: compound literals, statement expressions,
members of structure values, over C5's heap): ccomp's Mir of the program, linked with ccomp's
C library (`ccompMirRt`, `Runtime.lean`), is valid at the read-back convention for C6. It is
scored with the number of programs `checkC6` accepts.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem

/-- **The Ail → Mir validator for C6 is sound over ccomp's pipeline with its C library**
(goal 1, by translation validation, on the C6 rung): whenever `checkC6` accepts a program,
ccomp's Mir for it, linked with ccomp's C library, is valid at the read-back convention for C6
and has a behaviour. -/
def ccomp_rt_tv_sound_c6 : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, checkC6 p = true →
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C6.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty

end Silmaril.Compile.Targets
