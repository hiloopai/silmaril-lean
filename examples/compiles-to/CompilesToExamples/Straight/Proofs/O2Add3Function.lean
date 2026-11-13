module

public import CompilesToExamples.Straight.Proofs.O2Add3Seg0
public import CompilesToExamples.Straight.Proofs.Add3CanonicalSafe
public import Silmaril.Project.Shapes.CompilesTo.Thms

/-! `examples/compiles-to/straight/straight.c`, `O2`, `add3`: the function rows from its 1 segment(s).
`FnData.compilesToCanonical_of_segments` closes the canonical-entry row
(`c.compiles_to.canonical_entry`); `FnData.compilesTo_of_segments` gives the `c.compiles_to` row
from `Task.add3_safe` (safety from every entry), which stays open. -/

namespace CompilesToExamples.Straight.O2

open Silmaril.Project.CompilesTo Silmaril.Project.Shapes.CompilesTo

/-- Every segment of `add3` (none past point 0). -/
public theorem add3_segments (k : Nat) : SegmentSim Silmaril.X86.Open.isa add3 k :=
  match k with
  | 0 => add3_seg_0
  | _ + 1 => add3.segment_none (by simp [add3])

/-- The placement of `add3` can be entered for every argument tuple. -/
public theorem add3_enterable : Silmaril.Project.Shapes.SysV.Enterable Silmaril.X86.Open.isa
    add3.placement add3.sig add3.frame :=
  Silmaril.Project.Shapes.SysV.Enterable.of_fits (fun _ => trivial) (by decide) (by decide)
    (by decide)

/-- **`add3` at `O2` implements its C function from the canonical entry.** -/
public theorem add3_canonical : Task.add3_canonical :=
  add3.compilesToCanonical_of_segments (by decide) rfl add3_segments add3_enterable (by decide) (by decide +kernel)
    (by decide) (by decide +kernel) add3Args add3_args_safe

/-- **`add3` at `O2` implements its C function** (`c.compiles_to`), given that it is safe from
every entry (`Task.add3_safe`, open). -/
public theorem add3_compiles_to_of (h : Task.add3_safe) : Task.add3_compiles_to :=
  add3.compilesTo_of_segments (by decide) rfl add3_segments add3_enterable (by decide) (by decide +kernel)
    (by decide) (by decide +kernel) h

end CompilesToExamples.Straight.O2
