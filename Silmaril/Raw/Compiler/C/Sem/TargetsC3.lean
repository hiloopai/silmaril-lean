module

public import Silmaril.Compiler.C.Sem.Runtime.Defs
public import Silmaril.Compiler.C.Sem.Validator.Defs
public import Silmaril.Compiler.C.Sem.C3.Defs
@[expose] public section

/-!
# The validator target for the C3 rung

`Targets.ccomp_rt_tv_sound_c2` (`TargetsC2.lean`) with `checkC2` replaced by `checkC3` and
the C2 semantics by the C3 semantics (`C3.lean`, real floating types): ccomp's Mir of the
program, linked with ccomp's C library (`ccompMirRt`, `Runtime.lean`), is valid at the
read-back convention for C3. It is scored with the number of programs `checkC3` accepts.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem

/-- **The Ail → Mir validator for C3 is sound over ccomp's pipeline with its C library**
(goal 1, by translation validation, on the C3 rung): whenever `checkC3` accepts a program,
ccomp's Mir for it, linked with ccomp's C library, is valid at the read-back convention for C3
and has a behaviour. -/
def ccomp_rt_tv_sound_c3 : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, checkC3 p = true →
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C3.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty

end Silmaril.Compile.Targets
