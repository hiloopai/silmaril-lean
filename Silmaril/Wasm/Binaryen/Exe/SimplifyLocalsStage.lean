module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteAny

@[expose] public section

/-! # SimplifyLocals: the stage contract

`simplifyLocals_stageOk` is the `StageOk` contract of the registry row
(`PassRegistry.lean`), proved for the tee-drop part of SimplifyLocals,
`SimplifyLocalsLite.teeDrop` (`Pass/SimplifyLocalsLite.lean`): `drop (local.tee x v)`
becomes `local.set x v` in functions with scalar/SIMD locals; reference-local bodies
are preserved. Validity is `SimplifyLocalsLite.teeDrop_ok`, and export
equivalence `SimplifyLocalsLite.teeDrop_sound_any`: simulations in both directions,
specialized from every numerical profile to this stage's deterministic one. A leaf
file, imported by `Exe/PipelineSound.lean`.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Numerics

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- **SimplifyLocals is a sound stage.** -/
-- FLAG(statement-change): the stage is the tee-drop rewrite `SimplifyLocalsLite.teeDrop`,
-- not the set-sinking `simplifyLocals` (a separate general local-simplification pass (not included in this package), `local.set x v;
-- local.get x` to `local.tee x v`). Sinking has no frame-equal code simulation in either
-- direction: with the tee on the left its expansion keeps the frame and grows the code
--, and with the set on the left the pending `local.get x` is related
-- to the value only under the updated frame. Its contract stays open.
theorem simplifyLocals_stageOk : StageOk o H SimplifyLocalsLite.teeDrop :=
  fun _ hm => ⟨SimplifyLocalsLite.teeDrop_ok hm.ok, SimplifyLocalsLite.teeDrop_sound_any hm.ok⟩

end Silmaril.Wasm.Binaryen.Exe
