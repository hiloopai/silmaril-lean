module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.CodeFoldingSound

@[expose] public section

/-! # CodeFolding: the stage contract

`codeFolding_stageOk` is the `StageOk` contract of the registry row (`PassRegistry.lean`).
Validity and export equivalence are `CodeFolding.codeFolding_sound`
(`Binaryen/CodeFoldingSound.lean`): the hoisted tails are closed void trees, the arms
never branch out or return, and the block-unwrap simulation extended with folded `if`s
relates each body to its result. A leaf file, imported by `Exe/PipelineSound.lean`.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Numerics

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- **CodeFolding is a sound stage.** -/
theorem codeFolding_stageOk : StageOk o H codeFolding :=
  fun _ hm => CodeFolding.codeFolding_sound o H hm.ok

end Silmaril.Wasm.Binaryen.Exe
