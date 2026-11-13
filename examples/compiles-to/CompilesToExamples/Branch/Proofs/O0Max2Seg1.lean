module

public import CompilesToExamples.Branch.Defs
public import CompilesToExamples.Branch.Proofs.Elaborates
public import Silmaril.Project.CompilesTo.Thms

/-! `examples/compiles-to/branch/branch.c`, `O0`, `max2`, segment 1 (line 4: `if (b > a)`, to
line 5 or line 7): `FnData.segment_if_gt` (Core ↔ x86), and its composition with C ↔ Core
(C ↔ x86). -/

namespace CompilesToExamples.Branch.O0

open Silmaril.Project.CompilesTo Silmaril.Project.Shapes.CompilesTo

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- **Core ↔ x86**, segment 1 of `max2`. -/
public theorem max2_seg_1 : Task.max2_seg_1 :=
  FnData.segment_if_gt max2 (k := 1) (jT := 2) (jF := 3) (iy := 1) (iz := 0)
    (dy := 0xfffffff8) (dz := 0xfffffffc) (ny := 8) (nz := 4) (rel := 0x5)
    (hp := rfl) (hkind := rfl) (hqT := rfl) (hqTk := rfl) (hqF := rfl) (hqFk := rfl)
    (hoy' := rfl) (hoz' := rfl) (hif := by decide +kernel) (harms := rfl) (hdy := rfl)
    (hdz := rfl) (hsy := rfl) (hsz := rfl) (hoffy := by decide) (hoffz := by decide)
    (hdispy := by decide) (hdispz := by decide) (hny := by decide) (hnz := by decide)
    (hc1 := by decide +kernel) (hc2 := by decide +kernel) (hc3 := by decide +kernel)
    (hqToff := rfl) (hqFoff := by decide) (hmid := by decide) (hfit := by decide)
    (hpts := by decide) (haddr := by decide)

/-- **C ↔ x86**, segment 1 of `max2`: C ↔ Core (function and point) and Core ↔ x86. -/
public theorem max2_seg_1_from_c : Task.max2_seg_1_from_c :=
  ⟨elaborates_max2, max2_point_1, max2_seg_1⟩

end CompilesToExamples.Branch.O0
