module

public import Silmaril.Process.CLI.Loaded.Defs

/-!
# A loaded `CLI.Image`: facts

PROVED (standard axioms):

* `Segment.memSize_le_contents`: a segment's contents span at least its memory size.
-/

@[expose] public section

namespace Silmaril.Process.CLI

/-- A segment's contents (file bytes, then zero fill) span at least its memory size. -/
theorem Segment.memSize_le_contents (s : Segment) : s.memSize ≤ s.contents.length := by
  simp only [Segment.contents, List.length_append, List.length_replicate]; omega

end Silmaril.Process.CLI
