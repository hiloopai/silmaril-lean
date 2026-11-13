module

public import CompilesToExamples.Branch.Defs
public import CompilesToExamples.Branch.Proofs.Elaborates
public import Silmaril.Project.CompilesTo.Thms

/-! `examples/compiles-to/branch/branch.c`, `O0`, `max2`, segment 2 (line 5: `return b;`, to the
return label): `FnData.segment_return` with `retRun_load_jmp` (Core ↔ x86), and its composition
with C ↔ Core (C ↔ x86). -/

namespace CompilesToExamples.Branch.O0

open Silmaril.Project.CompilesTo Silmaril.Project.Shapes.CompilesTo

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- **Core ↔ x86**, segment 2 of `max2`. -/
public theorem max2_seg_2 : Task.max2_seg_2 :=
  FnData.segment_return max2 (k := 2) (j := 4) (iv := 1) (nv := 8) (xs := [])
    (hp := rfl) (hkind := rfl) (hq := rfl) (hqkind := rfl) (hfrag := rfl)
    (hlab := by decide +kernel) (hov := rfl) (hretv := by decide +kernel)
    (hkill := by decide +kernel) (hnodup := by decide +kernel) (hdv := rfl) (hsv := rfl)
    (hoffv := by decide) (hnv := by decide) (hres := rfl)
    (hrun := fun k0 => retRun_load_jmp max2 k0 (dv := 0xfffffff8) (rel := 0x3) rfl (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))

/-- **C ↔ x86**, segment 2 of `max2`: C ↔ Core (function and point) and Core ↔ x86. -/
public theorem max2_seg_2_from_c : Task.max2_seg_2_from_c :=
  ⟨elaborates_max2, max2_point_2, max2_seg_2⟩

end CompilesToExamples.Branch.O0
