module

public import Silmaril.Compiler.C.Sem.Runtime.Defs
public import Silmaril.Compiler.C.Sem.Validator.Defs
@[expose] public section

/-!
# The validator target over ccomp's pipeline with its C library (frozen)

`Targets.ccomp_tv_sound` with `ccompMir` replaced by `ccompMirRt` (`Runtime.lean`): ccomp's Mir
of the program linked with ccomp's C library, as ccomp's real link builds it. It is scored like
`ccomp_tv_sound`, with the number of programs `checkC0` accepts.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem

/-- **The Ail → Mir validator is sound over ccomp's pipeline with its C library** (goal 1, by
translation validation): whenever `checkC0` accepts a program, ccomp's Mir for it, linked with
ccomp's C library, is valid at the read-back convention for C0 and has a behaviour. -/
def ccomp_rt_tv_sound : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, checkC0 p = true →
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C0.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty

end Silmaril.Compile.Targets
