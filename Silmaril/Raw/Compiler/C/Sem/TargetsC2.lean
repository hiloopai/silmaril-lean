module

public import Silmaril.Compiler.C.Sem.Runtime.Defs
public import Silmaril.Compiler.C.Sem.Validator.Defs
public import Silmaril.Compiler.C.Sem.C2.Defs
@[expose] public section

/-!
# The validator target for the C2 rung

`Targets.ccomp_rt_tv_sound_c1` (`TargetsC1.lean`) with `checkC1` replaced by `checkC2` and
the C1 semantics by the C2 semantics (`C2.lean`, structs and unions): ccomp's Mir of the
program, linked with ccomp's C library (`ccompMirRt`, `Runtime.lean`), is valid at the
read-back convention for C2. It is scored with the number of programs `checkC2` accepts.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem

/-- **The Ail → Mir validator for C2 is sound over ccomp's pipeline with its C library**
(goal 1, by translation validation, on the C2 rung): whenever `checkC2` accepts a program,
ccomp's Mir for it, linked with ccomp's C library, is valid at the read-back convention for C2
and has a behaviour. -/
def ccomp_rt_tv_sound_c2 : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, checkC2 p = true →
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C2.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty

end Silmaril.Compile.Targets
