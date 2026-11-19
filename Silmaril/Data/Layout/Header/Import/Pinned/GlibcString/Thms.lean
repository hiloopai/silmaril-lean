module

public import Silmaril.Data.Layout.Header.Import.Pinned.GlibcString.Defs
public import Silmaril.Data.Layout.Header.Import.Thms

/-! # `glibc-string.json`: the one kernel import

PROVED (standard axioms, `decide +kernel`): `import_glibcString`. The import of the pinned
`examples/headers/clang/glibc-string.json` with its provenance is the literal `GlibcString.entries`, with
no document error. This is the only theorem that parses the JSON: every other theorem about
`glibcString` rewrites with it and computes on the literal. -/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

set_option maxRecDepth 100000 in
theorem import_glibcString : glibcString = ⟨.parse glibcStringProv, GlibcString.entries, none⟩ :=
  have h : glibcString.entries = GlibcString.entries ∧ glibcString.error = none := by decide +kernel
  Imported.eq_of (ofJson_provenance _ _) h.1 h.2

end Silmaril.Data.Layout.Header.Import.Pinned

end
