module

public import Silmaril.Wasm.Perf.CoreMod.Defs
public import Silmaril.Wasm.Perf.CoreDecode.Thms

/-!
# `coreModF` is `Lower.coreMod`

`coreMod_eq_coreModF`, registered as `@[csimp]`: compiled code that imports this module calls
`coreModF` (one fast decode) for `Lower.coreMod`. `coreModF_eq` is the same equation the other
way round, for the definitions that call `coreModF` directly (`JcoTool.New`, `NewI`, `Adaptor`,
`AdaptorI`, `Perf.LowerF`).
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.CoreMod

open Silmaril.Wasm.Component.Binary

/-- **`coreModF` is `Lower.coreMod`**, used by the compiler in its place. -/
@[csimp] theorem coreMod_eq_coreModF : @Lower.coreMod = @coreModF := by
  funext bytes
  simp only [Lower.coreMod, coreModF, Silmaril.Wasm.Perf.CoreDecode.decodeF_eq]
  rfl

theorem coreModF_eq : @coreModF = @Lower.coreMod := coreMod_eq_coreModF.symm

end Silmaril.Wasm.Perf.CoreMod
