module

public import Silmaril.Wasm.Perf.LowerF.Defs
public import Silmaril.Wasm.Perf.CoreMod.Thms

/-!
# The copies of `section_`, `lower`, `parseComponent` are the originals

`parseComponent_eq_parseComponentF`, registered with `@[csimp]`, and its symmetric form
`parseComponentF_eq` for the definitions that call `parseComponentF` (`JcoTool.Check.irCheck`,
`JcoTool.Tool.validate`).
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.LowerF

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary

theorem sectionF_eq : sectionF = Lower.section_ := by
  funext sec
  cases sec <;> simp only [sectionF, Lower.section_, CoreMod.coreMod_eq_coreModF]

theorem lowerF_eq : lowerF = lower := by
  funext c
  simp only [lowerF, lower, sectionF_eq]

/-- **`parseComponentF` is `parseComponent`**, used by the compiler in its place. -/
@[csimp] theorem parseComponent_eq_parseComponentF : @parseComponent = @parseComponentF := by
  funext b
  simp only [parseComponent, parseComponentF, lowerF_eq]
  rfl

theorem parseComponentF_eq : @parseComponentF = @parseComponent :=
  parseComponent_eq_parseComponentF.symm

end Silmaril.Wasm.Perf.LowerF
