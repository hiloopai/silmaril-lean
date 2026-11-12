module

public import Silmaril.Wasm.Perf.CanonB.Defs
public import Silmaril.Wasm.Perf.EncodeB.Thms

/-!
# The `ByteArray` canonicity check is the canonicity check

`canonPkgF_eq : canonPkgF = SpliceX.canonPkg` (from `EncodeB.astXB_some_iff`), and
`canonTable_eq_canonTableF`, registered with `@[csimp]`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.EncodeB

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync

theorem canonPkgF_eq : canonPkgF = Silmaril.Wasm.Wac.SpliceX.canonPkg := by
  funext p
  unfold canonPkgF Silmaril.Wasm.Wac.SpliceX.canonPkg
  cases parseX p.2 with
  | error _ => rfl
  | ok a =>
    show (if astXB a = some p.2 then _ else _) = (if EncodeX.ast a = some p.2.data.toList then _ else _)
    by_cases hc : EncodeX.ast a = some p.2.data.toList
    · have h2 : astXB a = some p.2 := (astXB_some_iff a p.2).mpr hc
      simp only [hc, h2, ite_true]
    · have h2 : ¬astXB a = some p.2 := fun h => hc ((astXB_some_iff a p.2).mp h)
      simp only [hc, h2, ite_false]

/-- **`canonTableF` is `SpliceX.canonTable`**, used by the compiler in its place. -/
@[csimp] theorem canonTable_eq_canonTableF :
    @Silmaril.Wasm.Wac.SpliceX.canonTable = @canonTableF := by
  funext raw
  simp only [Silmaril.Wasm.Wac.SpliceX.canonTable, canonTableF, canonPkgF_eq]

end Silmaril.Wasm.Perf.EncodeB
