module

public import CompilesToExamples.Straight.Defs
public import CompilesToExamples.Straight.Proofs.Elaborates
public import Silmaril.Project.CompilesTo.Thms

/-! `examples/compiles-to/straight/straight.c`, `O0`, `add3`, segment 0 (the entry, to line 4):
`FnData.segment_entry` (Core ↔ x86), and its composition with C ↔ Core (C ↔ x86). -/

namespace CompilesToExamples.Straight.O0

open Silmaril.Project.CompilesTo Silmaril.Project.Shapes.CompilesTo

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- **Core ↔ x86**, segment 0 of `add3`. -/
public theorem add3_seg_0 : Task.add3_seg_0 :=
  FnData.segment_entry add3 (xs := ((add3.slotsAt 1).drop 3).map (·.sym))
    (sp := [(.rdi, 0xffffffec, 20), (.rsi, 0xffffffe8, 24), (.rdx, 0xffffffe4, 28)])
    (hp := rfl) (hk0 := rfl) (hf0 := rfl) (hq := rfl) (hqk := rfl) (hbody := rfl) (hcr := rfl)
    (hkeys := by decide +kernel) (hnodup := by decide +kernel) (hroom := by decide)
    (hsig := by decide) (hdefs := by decide +kernel) (hslots := by decide +kernel)
    (hsp := by decide +kernel) (hdisp := by decide) (hpw := by decide) (hsp0 := by decide)
    (hqoff := rfl) (hmid := by decide) (hmid' := by decide) (hpush := by decide +kernel)
    (hmov := by decide +kernel) (hfr := by decide) (hfit := by decide) (hpts := by decide)
    (haddr := by decide)

/-- **C ↔ x86**, segment 0 of `add3`: C ↔ Core (function and point) and Core ↔ x86. -/
public theorem add3_seg_0_from_c : Task.add3_seg_0_from_c :=
  ⟨elaborates_add3, add3_point_0, add3_seg_0⟩

end CompilesToExamples.Straight.O0
