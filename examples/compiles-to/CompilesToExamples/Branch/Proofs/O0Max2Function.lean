module

public import CompilesToExamples.Branch.Proofs.O0Max2Seg0
public import CompilesToExamples.Branch.Proofs.O0Max2Seg1
public import CompilesToExamples.Branch.Proofs.O0Max2Seg2
public import CompilesToExamples.Branch.Proofs.O0Max2Seg3
public import CompilesToExamples.Branch.Proofs.O0Max2Seg4
public import CompilesToExamples.Branch.Proofs.Max2CanonicalSafe
public import Silmaril.Project.Shapes.CompilesTo.Thms

/-! `examples/compiles-to/branch/branch.c`, `O0`, `max2`: the function rows from its 5 segment(s).
`FnData.compilesToCanonical_of_segments` closes the canonical-entry row
(`c.compiles_to.canonical_entry`); `FnData.compilesTo_of_segments` gives the `c.compiles_to` row
from `Task.max2_safe` (safety from every entry), which stays open. -/

namespace CompilesToExamples.Branch.O0

open Silmaril.Project.CompilesTo Silmaril.Project.Shapes.CompilesTo

/-- Every segment of `max2` (none past point 4). -/
public theorem max2_segments (k : Nat) : SegmentSim Silmaril.X86.Open.isa max2 k :=
  match k with
  | 0 => max2_seg_0
  | 1 => max2_seg_1
  | 2 => max2_seg_2
  | 3 => max2_seg_3
  | 4 => max2_seg_4
  | _ + 5 => max2.segment_none (by simp [max2])

/-- The placement of `max2` can be entered for every argument tuple. -/
public theorem max2_enterable : Silmaril.Project.Shapes.SysV.Enterable Silmaril.X86.Open.isa
    max2.placement max2.sig max2.frame :=
  Silmaril.Project.Shapes.SysV.Enterable.of_fits (fun _ => trivial) (by decide) (by decide)
    (by decide)

/-- **`max2` at `O0` implements its C function from the canonical entry.** -/
public theorem max2_canonical : Task.max2_canonical :=
  max2.compilesToCanonical_of_segments (by decide) rfl max2_segments max2_enterable (by decide) (by decide +kernel)
    (by decide) (by decide +kernel) max2Args max2_args_safe

/-- **`max2` at `O0` implements its C function** (`c.compiles_to`), given that it is safe from
every entry (`Task.max2_safe`, open). -/
public theorem max2_compiles_to_of (h : Task.max2_safe) : Task.max2_compiles_to :=
  max2.compilesTo_of_segments (by decide) rfl max2_segments max2_enterable (by decide) (by decide +kernel)
    (by decide) (by decide +kernel) h

end CompilesToExamples.Branch.O0
