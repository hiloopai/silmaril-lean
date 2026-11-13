module

public import Silmaril.Compiler.C.Sem.Runtime.Defs
public import Silmaril.Compiler.C.Sem.ValidatorC7.Defs
public import Silmaril.Compiler.C.Sem.C7.Defs
@[expose] public section

/-!
# The validator target for the C7 rung

`Targets.ccomp_rt_tv_sound_c6` (`TargetsC6.lean`) with `checkC6` replaced by `checkC7` and
the C6 semantics by the C7 semantics (`C7.lean`: stdio streams on the standard output and
error, floating `printf` conversions, `va_list` arguments of the printf
family, over C6): ccomp's Mir of the program, linked with ccomp's C library (`ccompMirRt`,
`Runtime.lean`), is valid at the read-back convention for C7. It is scored with the number of
programs `checkC7` accepts.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem

/-- **The Ail → Mir validator for C7 is sound over ccomp's pipeline with its C library**
(goal 1, by translation validation, on the C7 rung): whenever `checkC7` accepts a program,
ccomp's Mir for it, linked with ccomp's C library, is valid at the read-back convention for C7
and has a behaviour. -/
def ccomp_rt_tv_sound_c7 : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, checkC7 p = true →
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C7.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty

end Silmaril.Compile.Targets
