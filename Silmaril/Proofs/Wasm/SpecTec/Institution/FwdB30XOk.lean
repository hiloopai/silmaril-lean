module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XTables

/-!
# The checks hold at the shapes of `pureCombos` and `readCombos`

Kernel `decide` on the `nonV` tables (`pureOk_eq`, `readOk_eq`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30X

open Silmaril.SpecTec.IL hiding Id Prod

/-- `pureOk` at every shape of `pureCombos`. -/
theorem pureCombos_ok {k : Nat} {t : MixopS} (h : (k, t) ∈ pureCombos) : pureOk k t = true := by
  have hall : pureCombos.all (fun p => pureOkN p.1 p.2) = true := by decide +kernel
  rw [pureOk_eq]
  exact List.all_eq_true.1 hall (k, t) h

/-- `readOk` at every shape of `readCombos`. -/
theorem readCombos_ok {k : Nat} {t : MixopS} (h : (k, t) ∈ readCombos) : readOk k t = true := by
  have hall : readCombos.all (fun p => readOkN p.1 p.2) = true := by decide +kernel
  rw [readOk_eq]
  exact List.all_eq_true.1 hall (k, t) h

end Silmaril.Wasm.SpecTec.Institution.FwdB30X
