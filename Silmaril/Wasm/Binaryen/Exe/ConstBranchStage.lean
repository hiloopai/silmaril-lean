module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.ConstBranchAny

@[expose] public section

/-! # ConstBranch: the stage contract

`constBranch_stageOk` is the `StageOk` contract of the appended registry row
`const-branch` (`PassRegistry.lean`), proved for `ConstBranch.constBranchChecked`
(`Pass/ConstBranch.lean`): `i32.const c; if bt A B` becomes `block bt A` or `block bt B`,
and `i32.const c; br_if l` becomes `br l` or `nop`. Validity is the validator's check,
export equivalence `ConstBranch.constBranchChecked_sound_any`: two simulations
at the same arbitrary numerical profile, specialized to the existing stage contract.
A leaf file, imported by `Exe/PipelineSound.lean`.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Numerics

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- **ConstBranch is a sound stage.** -/
theorem constBranch_stageOk : StageOk o H ConstBranch.constBranchChecked :=
  fun _ hm => ConstBranch.constBranchChecked_sound_any hm.ok

end Silmaril.Wasm.Binaryen.Exe
