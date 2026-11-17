module

public import Silmaril.Data.Layout.Header.Import.Pinned.ZlibHosted.Defs
public import Silmaril.Data.Layout.Header.Import.Thms

/-! # `zlib-hosted.json`: the one kernel import

PROVED (standard axioms, `decide +kernel`): `import_zlibHosted`. The import of the pinned
`examples/headers/clang/zlib-hosted.json` with its provenance is the literal `ZlibHosted.entries`, with
no document error. This is the only theorem that parses the JSON: every other theorem about
`zlibHosted` rewrites with it and computes on the literal. -/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

set_option maxRecDepth 100000 in
theorem import_zlibHosted : zlibHosted = ⟨.parse zlibHostedProv, ZlibHosted.entries, none⟩ :=
  have h : zlibHosted.entries = ZlibHosted.entries ∧ zlibHosted.error = none := by decide +kernel
  Imported.eq_of (ofJson_provenance _ _) h.1 h.2

end Silmaril.Data.Layout.Header.Import.Pinned

end
