module

public import CompilesToExamples.Straight.Defs
public import CompilesToExamples.Straight.Proofs.Elaborates
public import Silmaril.Project.CompilesTo.Thms

/-! `examples/compiles-to/straight/straight.c`, `O0`, `add3`, segment 3 (line 6: `return t;`, to the
return label): `FnData.segment_return` with `retRun_load` (Core ↔ x86), and its composition with
C ↔ Core (C ↔ x86). -/

namespace CompilesToExamples.Straight.O0

open Silmaril.Project.CompilesTo Silmaril.Project.Shapes.CompilesTo

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- **Core ↔ x86**, segment 3 of `add3`. -/
public theorem add3_seg_3 : Task.add3_seg_3 :=
  FnData.segment_return add3 (k := 3) (j := 4) (iv := 4) (nv := 8)
    (xs := ((add3.slotsAt 3).drop 3).map (·.sym))
    (hp := rfl) (hkind := rfl) (hq := rfl) (hqkind := rfl) (hfrag := rfl)
    (hlab := by decide +kernel) (hov := rfl) (hretv := by decide +kernel)
    (hkill := by decide +kernel) (hnodup := by decide +kernel) (hdv := rfl) (hsv := rfl)
    (hoffv := by decide) (hnv := by decide) (hres := rfl)
    (hrun := fun k0 => retRun_load add3 k0 (dv := 0xfffffff8) rfl (by decide) (by decide)
      (by decide) rfl (by decide))

/-- **C ↔ x86**, segment 3 of `add3`: C ↔ Core (function and point) and Core ↔ x86. -/
public theorem add3_seg_3_from_c : Task.add3_seg_3_from_c :=
  ⟨elaborates_add3, add3_point_3, add3_seg_3⟩

end CompilesToExamples.Straight.O0
