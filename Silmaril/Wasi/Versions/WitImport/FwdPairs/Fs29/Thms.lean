module

public import Silmaril.Wasi.Versions.WitImport.Fwd.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables29.Defs

@[expose] public section

/-!
# Forwarding pairs, computed once: fs (0.2.9)

Each `fwdPairs P Q` of `Silmaril.Wasi.Versions.WitImport.Fwd.Thms` is stated here as a literal
list, checked by the kernel (`decide +kernel`), and `FwdOk` is checked on that literal. The
pairs are split over several modules so each stays under the module time budget; `Fwd.Thms`
assembles `fwdOk_all` and the name lists from these equations by rewriting. The literals were
printed by evaluating `fwdPairs` (not trusted: the kernel checks each equation).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- Forwarding pairs, 0.3.2 `fs` over 0.2.9. -/
theorem fwdPairs_fs3_29 : fwdPairs fs29P fs3P =
    [(⟨"wasi:filesystem/types@0.3.2", "[method]descriptor.is-same-object"⟩,
       ⟨"wasi:filesystem/types", "[method]descriptor.is-same-object"⟩),
      (⟨"wasi:filesystem/preopens@0.3.2", "get-directories"⟩,
       ⟨"wasi:filesystem/preopens", "get-directories"⟩)] := by
  decide +kernel

/-- The pairs of 0.3.2 `fs` over 0.2.9 are forwardable. -/
theorem fwdOk_fs3_29 : FwdOk fs29P fs3P (fwdPairs fs29P fs3P) = true := by
  rw [fwdPairs_fs3_29]
  decide +kernel

/-- Forwarding pairs, 0.2.9 `fs` over 0.3.2. -/
theorem fwdPairs_fs29 : fwdPairs fs3P fs29P =
    [(⟨"wasi:filesystem/types", "[method]descriptor.is-same-object"⟩,
       ⟨"wasi:filesystem/types@0.3.2", "[method]descriptor.is-same-object"⟩),
      (⟨"wasi:filesystem/preopens", "get-directories"⟩,
       ⟨"wasi:filesystem/preopens@0.3.2", "get-directories"⟩)] := by
  decide +kernel

/-- The pairs of 0.2.9 `fs` over 0.3.2 are forwardable. -/
theorem fwdOk_fs29 : FwdOk fs3P fs29P (fwdPairs fs3P fs29P) = true := by
  rw [fwdPairs_fs29]
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
