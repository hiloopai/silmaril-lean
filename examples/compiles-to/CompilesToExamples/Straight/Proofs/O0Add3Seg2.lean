module

public import CompilesToExamples.Straight.Defs
public import CompilesToExamples.Straight.Proofs.Elaborates
public import Silmaril.Project.CompilesTo.Thms

/-! `examples/compiles-to/straight/straight.c`, `O0`, `add3`, segment 2 (line 5: `int t = s + c;`):
`FnData.segment_init_add` (Core ↔ x86), and its composition with C ↔ Core (C ↔ x86). -/

namespace CompilesToExamples.Straight.O0

open Silmaril.Project.CompilesTo Silmaril.Project.Shapes.CompilesTo

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- **Core ↔ x86**, segment 2 of `add3`. -/
public theorem add3_seg_2 : Task.add3_seg_2 :=
  FnData.segment_init_add add3 (k := 2) (iy := 3) (iz := 2) (ix := 4)
    (dy := 0xfffffffc) (dz := 0xffffffe4) (dx := 0xfffffff8) (ny := 4) (nz := 28) (nx := 8)
    (hp := rfl) (hkind := rfl) (hq := rfl) (hoy' := rfl) (hoz' := rfl) (hox' := rfl)
    (hqkind := rfl) (hinit := by decide +kernel) (hdy := rfl) (hdz := rfl) (hsy := rfl) (hsz := rfl)
    (hoffy := by decide) (hoffz := by decide) (hoffx := by decide)
    (hdispy := by decide) (hdispz := by decide) (hdispx := by decide)
    (hny := by decide) (hnz := by decide) (hnx4 := by decide) (hnx := by decide)
    (hapart := by decide) (hsame := by decide) (hin := by decide)
    (hc1 := by decide) (hc2 := by decide) (hc3 := by decide) (hc4 := by decide)
    (hqoff := rfl) (hfit := by decide) (hmid := by decide) (hpts := by decide)
    (haddr := by decide)

/-- **C ↔ x86**, segment 2 of `add3`: C ↔ Core (function and point) and Core ↔ x86. -/
public theorem add3_seg_2_from_c : Task.add3_seg_2_from_c :=
  ⟨elaborates_add3, add3_point_2, add3_seg_2⟩

end CompilesToExamples.Straight.O0
