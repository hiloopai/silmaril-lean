module

public import Silmaril.Compiler.C.Sem.Runtime.Defs
public import Silmaril.Compiler.C.Sem.Validator.Defs
public import Silmaril.Compiler.C.Sem.C4.Defs
@[expose] public section

/-!
# The validator target for the C4 rung

`Targets.ccomp_rt_tv_sound_c3` (`TargetsC3.lean`) with `checkC3` replaced by `checkC4` and
the C3 semantics by the C4 semantics (`C4.lean`, function pointers and typed variadic calls):
ccomp's Mir of the program, linked with ccomp's C library (`ccompMirRt`, `Runtime.lean`), is
valid at the read-back convention for C4. It is scored with the number of programs `checkC4`
accepts.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem

/-- **The Ail → Mir validator for C4 is sound over ccomp's pipeline with its C library**
(goal 1, by translation validation, on the C4 rung): whenever `checkC4` accepts a program,
ccomp's Mir for it, linked with ccomp's C library, is valid at the read-back convention for C4
and has a behaviour. -/
def ccomp_rt_tv_sound_c4 : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, checkC4 p = true →
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C4.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty

end Silmaril.Compile.Targets
