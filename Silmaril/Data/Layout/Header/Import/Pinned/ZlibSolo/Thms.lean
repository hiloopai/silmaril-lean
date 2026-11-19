module

public import Silmaril.Data.Layout.Header.Import.Pinned.ZlibSolo.Defs
public import Silmaril.Data.Layout.Header.Import.Thms

/-! # `zlib-solo.json`: the one kernel import

PROVED (standard axioms, `decide +kernel`): `import_zlibSolo`. The import of the pinned
`examples/headers/clang/zlib-solo.json` with its provenance is the literal `ZlibSolo.entries`, with
no document error. This is the only theorem that parses the JSON: every other theorem about
`zlibSolo` rewrites with it and computes on the literal. -/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

set_option maxRecDepth 100000 in
theorem import_zlibSolo : zlibSolo = ⟨.parse zlibSoloProv, ZlibSolo.entries, none⟩ :=
  have h : zlibSolo.entries = ZlibSolo.entries ∧ zlibSolo.error = none := by decide +kernel
  Imported.eq_of (ofJson_provenance _ _) h.1 h.2

end Silmaril.Data.Layout.Header.Import.Pinned

end
