module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.PrecomputeLiteSim

@[expose] public section

/-! # Precompute: the anchored addition stage contract

`precompute_stageOk` proves the registry contract for constant integer addition
when the following sequence has a VacuumLite anchor. Other integer folds and
unanchored folding remain outside this stage. The proof uses a code simulation
in both directions and preserves typing through the existing FoldCase result.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Numerics

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

-- FLAG(statement-change): this contract is for PrecomputeLite.precomputeLite,
-- the anchored constant-addition subset, replacing the stated full precompute
-- contract. The full Pass/Precompute.lean transformation is still unproved.
/-- Anchored constant addition is a sound stage. -/
theorem precompute_stageOk : StageOk o H PrecomputeLite.precomputeLite :=
  fun _ hm => ⟨PrecomputeLite.precomputeLite_ok hm.ok,
    PrecomputeLite.precomputeLite_sound hm.ok closedHost closedHost_codeParametric⟩

end Silmaril.Wasm.Binaryen.Exe
