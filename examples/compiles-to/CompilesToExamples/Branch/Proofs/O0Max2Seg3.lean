module

public import CompilesToExamples.Branch.Defs
public import CompilesToExamples.Branch.Proofs.Elaborates
public import Silmaril.Project.CompilesTo.Thms

/-! `examples/compiles-to/branch/branch.c`, `O0`, `max2`, segment 3 (line 7: `return a;`, to the
return label): `FnData.segment_return` with `retRun_load` (Core ↔ x86), and its composition with
C ↔ Core (C ↔ x86). -/

namespace CompilesToExamples.Branch.O0

open Silmaril.Project.CompilesTo Silmaril.Project.Shapes.CompilesTo

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- **Core ↔ x86**, segment 3 of `max2`. -/
public theorem max2_seg_3 : Task.max2_seg_3 :=
  FnData.segment_return max2 (k := 3) (j := 4) (iv := 0) (nv := 4) (xs := [])
    (hp := rfl) (hkind := rfl) (hq := rfl) (hqkind := rfl) (hfrag := rfl)
    (hlab := by decide +kernel) (hov := rfl) (hretv := by decide +kernel)
    (hkill := by decide +kernel) (hnodup := by decide +kernel) (hdv := rfl) (hsv := rfl)
    (hoffv := by decide) (hnv := by decide) (hres := rfl)
    (hrun := fun k0 => retRun_load max2 k0 (dv := 0xfffffffc) rfl (by decide) (by decide)
      (by decide) rfl (by decide))

/-- **C ↔ x86**, segment 3 of `max2`: C ↔ Core (function and point) and Core ↔ x86. -/
public theorem max2_seg_3_from_c : Task.max2_seg_3_from_c :=
  ⟨elaborates_max2, max2_point_3, max2_seg_3⟩

end CompilesToExamples.Branch.O0
