module

public import Silmaril.X86.Ladder.Pinned.Thms
public import Silmaril.X86.Ladder.Pinned.LeafArith
public import Silmaril.X86.Ladder.LeafArith.Transcript

/-! # Binary tie of rung 01 (`leaf-arith`)

The transcribed code region of `examples/elf-ladder/01-leaf-arith` (`LeafArith.Transcript.region`)
is the bytes the public LPS loader loads at its address from the committed `-O2` executable
(`Pinned.LeafArith.exe`), by one kernel evaluation (`checkAll`), as for the other rungs in
`Pinned/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Ladder.Pinned

open Silmaril.X86.Ladder

/-- The slices of rung 01 that a proof uses. -/
def leafArithSlices : List (String × Nat × List (BitVec 8)) :=
  [("rx", LeafArith.Transcript.region.base, LeafArith.Transcript.region.bytes)]

set_option maxRecDepth 100000 in
theorem leafArith_checked : checkAll LeafArith.exe leafArithSlices = true := by decide +kernel

theorem leafArith_region :
    LoadedAt LeafArith.exe "rx" LeafArith.Transcript.region.base
      LeafArith.Transcript.region.bytes :=
  checkAll_sound leafArith_checked (by simp [leafArithSlices])

end Silmaril.X86.Ladder.Pinned
