module

public import Silmaril.Wasm.FX.Asyncify.Tool.Fits.Defs

/-!
# The asyncified program stays in bounds when `sp` wraps: definitions

`DepthBound` (`Silmaril.Wasm.FX.Asyncify.Tool.Sys`) asks that every reachable source state needs
less than `2 ^ 32` bytes of shadow stack, `SB + 4 F · depth < 2 ^ 32`, so that every record
*ends* below `2 ^ 32`. `DepthBoundW` only asks that every record *starts* below `2 ^ 32`,
`SB + 4 F · depth < 2 ^ 32 + 4 F`: the `sp` after the last record of an unwinding may then wrap
around, but it is only ever popped again (modulo `2 ^ 32`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

/-- Every reachable source state's records start below `2 ^ 32`. -/
def DepthBoundW {σ : Type} (P : Prog) (H : Host σ) (x : Cfg × σ) : Prop :=
  ∀ n y, runN (srcStep P.env H) n x = .next y →
    P.sb + 4 * P.frameWords * y.1.frames.length < 2 ^ 32 + 4 * P.frameWords

end Silmaril.Wasm.FX.Asyncify.Tool
