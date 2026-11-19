module

public import Silmaril.Data.Layout.Header.Import.Pinned.Probe.Defs
public import Silmaril.Data.Layout.Header.Import.Thms

/-! # `probe.json`: the one kernel import

PROVED (standard axioms, `decide +kernel`): `import_probe`. The import of the pinned
`examples/headers/clang/probe.json` with its provenance is the literal `Probe.entries`, with
no document error. This is the only theorem that parses the JSON: every other theorem about
`probe` rewrites with it and computes on the literal. -/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

set_option maxRecDepth 100000 in
theorem import_probe : probe = ⟨.parse probeProv, Probe.entries, none⟩ :=
  have h : probe.entries = Probe.entries ∧ probe.error = none := by decide +kernel
  Imported.eq_of (ofJson_provenance _ _) h.1 h.2

end Silmaril.Data.Layout.Header.Import.Pinned

end
