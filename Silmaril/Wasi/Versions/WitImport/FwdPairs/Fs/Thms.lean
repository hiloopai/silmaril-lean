module

public import Silmaril.Wasi.Versions.WitImport.Fwd.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables29.Defs

@[expose] public section

/-!
# Forwarding pairs, computed once: fs

Each `fwdPairs P Q` of `Silmaril.Wasi.Versions.WitImport.Fwd.Thms` is stated here as a literal
list, checked by the kernel (`decide +kernel`), and `FwdOk` is checked on that literal. The
pairs are split over several modules so each stays under the module time budget; `Fwd.Thms`
assembles `fwdOk_all` and the name lists from these equations by rewriting. The literals were
printed by evaluating `fwdPairs` (not trusted: the kernel checks each equation).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- Forwarding pairs, 0.3.2 `fs` over 0.2.12. -/
theorem fwdPairs_fs3 : fwdPairs fs2P fs3P =
    [(⟨"wasi:filesystem/types@0.3.2", "[method]descriptor.is-same-object"⟩,
       ⟨"wasi:filesystem/types", "[method]descriptor.is-same-object"⟩),
      (⟨"wasi:filesystem/preopens@0.3.2", "get-directories"⟩,
       ⟨"wasi:filesystem/preopens", "get-directories"⟩)] := by
  decide +kernel

/-- The pairs of 0.3.2 `fs` over 0.2.12 are forwardable. -/
theorem fwdOk_fs3 : FwdOk fs2P fs3P (fwdPairs fs2P fs3P) = true := by
  rw [fwdPairs_fs3]
  decide +kernel

/-- Forwarding pairs, 0.2.12 `fs` over 0.3.2. -/
theorem fwdPairs_fs2 : fwdPairs fs3P fs2P =
    [(⟨"wasi:filesystem/types", "[method]descriptor.is-same-object"⟩,
       ⟨"wasi:filesystem/types@0.3.2", "[method]descriptor.is-same-object"⟩),
      (⟨"wasi:filesystem/preopens", "get-directories"⟩,
       ⟨"wasi:filesystem/preopens@0.3.2", "get-directories"⟩)] := by
  decide +kernel

/-- The pairs of 0.2.12 `fs` over 0.3.2 are forwardable. -/
theorem fwdOk_fs2 : FwdOk fs3P fs2P (fwdPairs fs3P fs2P) = true := by
  rw [fwdPairs_fs2]
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
