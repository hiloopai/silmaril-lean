module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track casts: definitions

Track casts proves the cast leaf `Target.Casts` of the round-6 target at the backend reading
`Round6.Int.backend` (`Reading.SStepB`), conditionally on `Reading.RefOkBB`.
Track reading proved the cast rules at the top level (`Reading.castsFwdB_of`,
`Reading.castsBwdB_of`); this track carries them through the context rules.

* `castA`, `castB`: a decidable reading of `Target.CastRedex` (`castB` holds of every cast redex,
  `Round6.Casts.castB_of_castRedex`). It is what the Core-side recursion refutes the other
  constructors of `Step` with.
* `CastTop c c'`: the eight Core steps of a cast instruction at the top level, `[ref r, cast] →
  …`.

See `docs/projects/spectec/README.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Casts

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

mutual
/-- An instruction that, after a prefix of values, makes its code a cast redex: a cast, or a
label, handler or frame whose body is a cast redex. -/
def castA : Admin → Bool
  | .plain i => Target.castInstr i
  | .label _ _ b => castB b
  | .handler _ _ b => castB b
  | .frame _ _ b => castB b
  | _ => false

/-- **A decidable reading of `Target.CastRedex`**: after a prefix of values, an instruction with
`castA`. -/
def castB : List Admin → Bool
  | [] => false
  | a :: l => castA a || (a.val?.isSome && castB l)
end

/-- **The eight Core steps of a cast instruction at the top level** (`Step.reference`'s
`testTrue`, `testFalse`, `castSucceed`, `castFail` and `Step`'s four `br_on_cast` rules). -/
inductive CastTop : Config H → Config H → Prop where
  /-- `ref.test`, true. -/
  | testTrue {s : Store H} {f : Frame} {r : Ref} {rt : RefType}
      (h : RefOk s r (f.module.instRef rt)) :
      CastTop ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 1]⟩
  /-- `ref.test`, false. -/
  | testFalse {s : Store H} {f : Frame} {r : Ref} {rt : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt)) :
      CastTop ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 0]⟩
  /-- `ref.cast`, success. -/
  | castSucceed {s : Store H} {f : Frame} {r : Ref} {rt : RefType}
      (h : RefOk s r (f.module.instRef rt)) :
      CastTop ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.ref r]⟩
  /-- `ref.cast`, failure. -/
  | castFail {s : Store H} {f : Frame} {r : Ref} {rt : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt)) :
      CastTop ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.trap]⟩
  /-- `br_on_cast`, success. -/
  | brOnCastSucceed {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : RefOk s r (f.module.instRef rt₂)) :
      CastTop ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ ⟨s, f, [.ref r, .plain (.br l)]⟩
  /-- `br_on_cast`, failure. -/
  | brOnCastFail {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt₂)) :
      CastTop ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩
  /-- `br_on_cast_fail`, success. -/
  | brOnCastFailSucceed {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : RefOk s r (f.module.instRef rt₂)) :
      CastTop ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩
  /-- `br_on_cast_fail`, failure. -/
  | brOnCastFailFail {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt₂)) :
      CastTop ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Casts
