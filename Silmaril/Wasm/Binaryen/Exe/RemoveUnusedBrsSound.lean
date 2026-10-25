module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardAny

@[expose] public section

/-! # RemoveUnusedBrs: the stage contract

`removeUnusedBrs_stageOk` is the `StageOk` contract of the registry row
(`PassRegistry.lean`), proved for the guard conversion `invertGuardsChecked`
(`Pass/RemoveUnusedBrs.lean`): an empty-typed `block` that opens with
`local.get x; br_if 0` becomes `local.get x; i32.eqz; if ... end`. Validity is the
validator's check; exact export equivalence specializes the two simulations in
`GuardSim.invertGuardsChecked_sound_any` at the existing deterministic profile.
The run function, validator guard and `StageOk` API are unchanged. A leaf file,
imported by `Exe/PipelineSound.lean`.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Numerics

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- **RemoveUnusedBrs is a sound stage.** -/
-- FLAG(statement-change): the stage is the guard conversion `invertGuardsChecked`, not
-- `removeUnusedBrs` (`Pass/RemoveUnusedBrs.lean`), which also splices branch-free
-- wrappers. Wrapper removal runs a body on one side and the same body under a label on
-- the other, which the closure simulation does not relate; its contract stays open.
theorem removeUnusedBrs_stageOk : StageOk o H invertGuardsChecked := by
  intro m hm
  exact GuardSim.invertGuardsChecked_sound_any hm.ok

end Silmaril.Wasm.Binaryen.Exe
