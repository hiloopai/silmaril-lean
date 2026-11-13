module

public import Silmaril.Compiler.C.Sem.Runtime.Defs
public import Silmaril.Compiler.C.Sem.Validator.Defs
public import Silmaril.Compiler.C.Sem.C5.Defs
@[expose] public section

/-!
# The validator target for the C5 rung

`Targets.ccomp_rt_tv_sound_c4` (`TargetsC4.lean`) with `checkC4` replaced by `checkC5` and
the C4 semantics by the C5 semantics (`C5.lean`, the heap: `malloc`, `calloc`, `realloc`,
`free`): ccomp's Mir of the program, linked with ccomp's C library (`ccompMirRt`,
`Runtime.lean`, whose allocator is part of the compiled program), is valid at the read-back
convention for C5. It is scored with the number of programs `checkC5` accepts.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem

/-- **The Ail → Mir validator for C5 is sound over ccomp's pipeline with its C library**
(goal 1, by translation validation, on the C5 rung): whenever `checkC5` accepts a program,
ccomp's Mir for it, linked with ccomp's C library, is valid at the read-back convention for C5
and has a behaviour. -/
def ccomp_rt_tv_sound_c5 : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, checkC5 p = true →
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C5.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty

end Silmaril.Compile.Targets
