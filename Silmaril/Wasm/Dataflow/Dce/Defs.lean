module

public import Silmaril.Wasm.Dataflow.LocalDce.Defs
public import Silmaril.Wasm.Dataflow.DropElim.Defs

/-!
# Two-pass liveness-based DCE for Wasm: definitions

`dce2 = dropElim ∘ localDce`:

1. `localDce` (`Silmaril.Wasm.Dataflow.LocalDce`): a dead `local.set x` becomes `drop` and a
   dead `local.tee x` is deleted. It has no lookahead; liveness of the source is used only
   for safety.
2. `dropElim` (`Silmaril.Wasm.Dataflow.DropElim`): a removable producer followed by `drop`
   becomes drops of its operands. It needs no liveness and keeps frames equal.

Each pass has a compositional simulation, and the correctness theorems of
`Silmaril.Wasm.Dataflow.Dce.Thms` chain them. The fused one-pass transform
(`Silmaril.Wasm.Dataflow.Fused`) has no such simulation.

Ported from an earlier development `Silmaril/Wasm/Dataflow/DceTwoPass.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm

/-- The two-pass DCE of a function body. -/
def dce2 (e : Expr) : Expr := dropElim (localDce e)

/-- `i32.const 1; local.tee 0; drop`, with local `0` dead afterwards. -/
def teeDropExample : Expr := [.intConst .i32 1, .localTee ⟨0⟩, .drop]

end Silmaril.Wasm.Dataflow
