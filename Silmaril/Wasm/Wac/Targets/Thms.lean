module

public import Silmaril.Wasm.Wac.Targets.Defs

/-!
# WAC targets checking: the decision procedure

`fits_iff`: `fits c w = true ↔ Fits c w`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Targets

open Silmaril.Wasm.Wit

theorem misfits_nil_iff (c w : Project.WorldType) :
    misfits c w = [] ↔ Fits c w := by
  simp only [misfits, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, Fits, Bool.and_eq_true,
    bne_iff_ne, ne_eq, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => Classical.byContradiction (h1 i hi),
      fun e he ht => Classical.byContradiction (h2 e he ht)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi hn => hn (h1 i hi), fun e he ht hn => hn (h2 e he ht)⟩

theorem fits_iff (c w : Project.WorldType) : fits c w = true ↔ Fits c w := by
  rw [fits, List.isEmpty_iff, misfits_nil_iff]

end Silmaril.Wasm.Wac.Targets
