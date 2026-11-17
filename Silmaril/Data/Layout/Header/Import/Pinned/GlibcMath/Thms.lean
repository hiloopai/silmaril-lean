module

public import Silmaril.Data.Layout.Header.Import.Pinned.GlibcMath.Defs
public import Silmaril.Data.Layout.Header.Import.Thms

/-! # `glibc-math.json`: the one kernel import

PROVED (standard axioms, `decide +kernel`): `import_glibcMath`. The import of the pinned
`examples/headers/clang/glibc-math.json` with its provenance is the literal `GlibcMath.entries`, with
no document error. This is the only theorem that parses the JSON: every other theorem about
`glibcMath` rewrites with it and computes on the literal.

**Cost.** The JSON is 294 120 bytes (623 declarations), about nine times `glibc-string.json`;
the kernel parses it in about four to five minutes (229 s locally, 290 s in CI). That is build
time on the critical path of every build that rebuilds this module, under the repository's CI
policy like any other. The heartbeat limit is raised to 400 000 for this theorem only
(deterministic: heartbeats count allocations, not time).
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem import_glibcMath : glibcMath = ⟨.parse glibcMathProv, GlibcMath.entries, none⟩ :=
  have h : glibcMath.entries = GlibcMath.entries ∧ glibcMath.error = none := by decide +kernel
  Imported.eq_of (ofJson_provenance _ _) h.1 h.2

end Silmaril.Data.Layout.Header.Import.Pinned

end
