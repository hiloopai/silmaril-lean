module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.IfSwapAny

@[expose] public section

/-! # OptimizeInstructions (peephole): the stage contract

`optimizeInstructions_stageOk` is the `StageOk` contract of the registry row
(`PassRegistry.lean`), proved for the arm swap `IfSwap.ifSwapChecked`
(`Pass/IfSwap.lean`): `i32.eqz; if bt A B` with a non-empty else arm becomes
`if bt B A`. Validity is the validator's check, export equivalence
`IfSwap.ifSwapChecked_sound_any`: two simulations at the same arbitrary
numerical profile (`IfSwapAny.lean`), specialized to the existing stage contract.
A leaf file, imported by `Exe/PipelineSound.lean`.

The full peephole table (a separate general peephole optimizer (not included in this package)) stays in neither pipeline: its
semantic proof needs the corrected contextual bridge described there.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Numerics

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- **OptimizeInstructions is a sound stage.** -/
-- FLAG(statement-change): the stage is the arm swap `IfSwap.ifSwapChecked`, not the
-- full peephole table `peephole` (a separate general peephole optimizer (not included in this package)), whose proof stays open.
theorem optimizeInstructions_stageOk : StageOk o H IfSwap.ifSwapChecked :=
  fun _ hm => IfSwap.ifSwapChecked_sound_any hm.ok

end Silmaril.Wasm.Binaryen.Exe
