module

public import Silmaril.Wasi.Versions.WitImport.Fwd.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables29.Defs

@[expose] public section

/-!
# Forwarding pairs, computed once: http

Each `fwdPairs P Q` of `Silmaril.Wasi.Versions.WitImport.Fwd.Thms` is stated here as a literal
list, checked by the kernel (`decide +kernel`), and `FwdOk` is checked on that literal. The
pairs are split over several modules so each stays under the module time budget; `Fwd.Thms`
assembles `fwdOk_all` and the name lists from these equations by rewriting. The literals were
printed by evaluating `fwdPairs` (not trusted: the kernel checks each equation).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- Forwarding pairs, 0.3.2 `http` over 0.2.12. -/
theorem fwdPairs_http3 : fwdPairs http2P http3P =
    [(⟨"wasi:http/types@0.3.2", "[constructor]fields"⟩,
       ⟨"wasi:http/types", "[constructor]fields"⟩),
      (⟨"wasi:http/types@0.3.2", "[method]fields.clone"⟩,
       ⟨"wasi:http/types", "[method]fields.clone"⟩),
      (⟨"wasi:http/types@0.3.2", "[constructor]request-options"⟩,
       ⟨"wasi:http/types", "[constructor]request-options"⟩)] := by
  decide +kernel

/-- The pairs of 0.3.2 `http` over 0.2.12 are forwardable. -/
theorem fwdOk_http3 : FwdOk http2P http3P (fwdPairs http2P http3P) = true := by
  rw [fwdPairs_http3]
  decide +kernel

/-- Forwarding pairs, 0.2.12 `http` over 0.3.2. -/
theorem fwdPairs_http2 : fwdPairs http3P http2P =
    [(⟨"wasi:http/types", "[constructor]fields"⟩,
       ⟨"wasi:http/types@0.3.2", "[constructor]fields"⟩),
      (⟨"wasi:http/types", "[method]fields.clone"⟩,
       ⟨"wasi:http/types@0.3.2", "[method]fields.clone"⟩),
      (⟨"wasi:http/types", "[constructor]request-options"⟩,
       ⟨"wasi:http/types@0.3.2", "[constructor]request-options"⟩)] := by
  decide +kernel

/-- The pairs of 0.2.12 `http` over 0.3.2 are forwardable. -/
theorem fwdOk_http2 : FwdOk http3P http2P (fwdPairs http3P http2P) = true := by
  rw [fwdPairs_http2]
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
