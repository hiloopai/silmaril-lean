module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.VacuumLiteSim

@[expose] public section

/-! # Vacuum: the stage contract

`vacuum_stageOk` is the `StageOk` contract of the registry row (`PassRegistry.lean`),
proved for the anchored vacuum `VacuumLite.vacuumLite` (`Pass/VacuumLite.lean`): `nop`
and the `drop` of an integer constant are removed where an anchor follows. Validity is
`VacuumLite.vacuumLite_ok` and export equivalence `VacuumLite.vacuumLite_sound`, a code
simulation in both directions (`VacuumLiteSim.lean`). A leaf file, imported by
`Exe/PipelineSound.lean`.

-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Numerics

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- **Vacuum is a sound stage.** -/
-- FLAG(statement-change): the stage is the anchored vacuum `VacuumLite.vacuumLite`, not
-- `vacuumModule false` (`Pass/Vacuum.lean`). The full pass removes trees whose removal
-- the closure simulation cannot match in the reverse direction (`[]` against `[nop]`
-- with no anchor, `drop` of an operator tree that may trap), so its contract stays open.
theorem vacuum_stageOk : StageOk o H VacuumLite.vacuumLite :=
  fun _ hm => ⟨VacuumLite.vacuumLite_ok hm.ok,
    VacuumLite.vacuumLite_sound hm.ok closedHost closedHost_codeParametric⟩

end Silmaril.Wasm.Binaryen.Exe
