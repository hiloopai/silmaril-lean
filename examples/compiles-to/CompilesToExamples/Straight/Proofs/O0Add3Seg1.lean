module

public import CompilesToExamples.Straight.Defs
public import CompilesToExamples.Straight.Proofs.Elaborates
public import Silmaril.Project.CompilesTo.Thms

/-! `examples/compiles-to/straight/straight.c`, `O0`, `add3`, segment 1 (line 4: `int s = a + b;`):
`FnData.segment_init_add` (Core ↔ x86), and its composition with C ↔ Core (C ↔ x86). -/

namespace CompilesToExamples.Straight.O0

open Silmaril.Project.CompilesTo Silmaril.Project.Shapes.CompilesTo

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- **Core ↔ x86**, segment 1 of `add3`. -/
public theorem add3_seg_1 : Task.add3_seg_1 :=
  FnData.segment_init_add add3 (k := 1) (iy := 0) (iz := 1) (ix := 3)
    (dy := 0xffffffec) (dz := 0xffffffe8) (dx := 0xfffffffc) (ny := 20) (nz := 24) (nx := 4)
    (hp := rfl) (hkind := rfl) (hq := rfl) (hoy' := rfl) (hoz' := rfl) (hox' := rfl)
    (hqkind := rfl) (hinit := by decide +kernel) (hdy := rfl) (hdz := rfl) (hsy := rfl) (hsz := rfl)
    (hoffy := by decide) (hoffz := by decide) (hoffx := by decide)
    (hdispy := by decide) (hdispz := by decide) (hdispx := by decide)
    (hny := by decide) (hnz := by decide) (hnx4 := by decide) (hnx := by decide)
    (hapart := by decide) (hsame := by decide) (hin := by decide)
    (hc1 := by decide) (hc2 := by decide) (hc3 := by decide) (hc4 := by decide)
    (hqoff := rfl) (hfit := by decide) (hmid := by decide) (hpts := by decide)
    (haddr := by decide)

/-- **C ↔ x86**, segment 1 of `add3`: C ↔ Core (function and point) and Core ↔ x86. -/
public theorem add3_seg_1_from_c : Task.add3_seg_1_from_c :=
  ⟨elaborates_add3, add3_point_1, add3_seg_1⟩

end CompilesToExamples.Straight.O0
