module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.ConstSelectAny

@[expose] public section

/-! Stage contract for constant-condition select and branch-table folding. -/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Numerics

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- Constant select/table folding is a sound stage. -/
theorem constSelect_stageOk : StageOk o H ConstSelect.constSelectChecked := by
  intro m hm
  exact ConstSelect.constSelectChecked_sound_any hm.ok

end Silmaril.Wasm.Binaryen.Exe
