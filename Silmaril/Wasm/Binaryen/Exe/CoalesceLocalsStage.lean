module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.CoalesceLocalsProfile

@[expose] public section

/-! # CoalesceLocals: the stage contract

`coalesceLocals_stageOk` is the `StageOk` contract of the registry row
(`PassRegistry.lean`), proved for the overwrite-anchored dead stores of CoalesceLocals,
`CoalesceLocalsLite.deadSetLite` (`Pass/CoalesceLocalsLite.lean`): a `local.set x v`
whose next sibling stores a constant into `x` becomes `drop v`. Validity is
`CoalesceLocalsLite.deadSetLite_ok`, and export equivalence
`CoalesceLocalsLite.deadSetLite_sound_profile`: the existing forward simulation and a
reverse simulation that completes transient source writes under runtime contexts. A leaf
file, imported by `Exe/PipelineSound.lean`.

The full liveness pass `coalesceLocals` and its contract are open work outside this restricted pass.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Numerics

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- **CoalesceLocals is a sound stage.** -/
-- FLAG(statement-change): the stage is the overwrite-anchored dead-store rewrite
-- `CoalesceLocalsLite.deadSetLite`, not the liveness pass `coalesceLocals`
--, whose contract stays open. A
-- dead store temporarily changes the frame of the original side alone. The
-- converse records the actual forced overwrite before resynchronizing frames.
theorem coalesceLocals_stageOk : StageOk o H CoalesceLocalsLite.deadSetLite :=
  fun _ hm => ⟨CoalesceLocalsLite.deadSetLite_ok hm.ok,
    CoalesceLocalsLite.deadSetLite_sound_profile hm.ok⟩

end Silmaril.Wasm.Binaryen.Exe
