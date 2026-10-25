module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.AddChainAny

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Numerics

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- Combining adjacent wrapping constant additions is a sound stage. -/
theorem addChain_stageOk : StageOk o H AddChain.addChainChecked :=
  fun _ hm => AddChain.addChainChecked_sound_any hm.ok

end Silmaril.Wasm.Binaryen.Exe
