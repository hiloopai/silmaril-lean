module

public import Silmaril.Wasi.Versions.WitImport.Fwd.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables29.Defs

@[expose] public section

/-!
# Forwarding pairs, computed once: sock (0.2.9)

Each `fwdPairs P Q` of `Silmaril.Wasi.Versions.WitImport.Fwd.Thms` is stated here as a literal
list, checked by the kernel (`decide +kernel`), and `FwdOk` is checked on that literal. The
pairs are split over several modules so each stays under the module time budget; `Fwd.Thms`
assembles `fwdOk_all` and the name lists from these equations by rewriting. The literals were
printed by evaluating `fwdPairs` (not trusted: the kernel checks each equation).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- Forwarding pairs, 0.3.2 `sock` over 0.2.9. -/
theorem fwdPairs_sock3_29 : fwdPairs sock29P sock3P =
    [] := by
  decide +kernel

/-- The pairs of 0.3.2 `sock` over 0.2.9 are forwardable. -/
theorem fwdOk_sock3_29 : FwdOk sock29P sock3P (fwdPairs sock29P sock3P) = true := by
  rw [fwdPairs_sock3_29]
  decide +kernel

/-- Forwarding pairs, 0.2.9 `sock` over 0.3.2. -/
theorem fwdPairs_sock29 : fwdPairs sock3P sock29P =
    [] := by
  decide +kernel

/-- The pairs of 0.2.9 `sock` over 0.3.2 are forwardable. -/
theorem fwdOk_sock29 : FwdOk sock3P sock29P (fwdPairs sock3P sock29P) = true := by
  rw [fwdPairs_sock29]
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
