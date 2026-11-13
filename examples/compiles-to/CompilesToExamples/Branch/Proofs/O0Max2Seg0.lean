module

public import CompilesToExamples.Branch.Defs
public import CompilesToExamples.Branch.Proofs.Elaborates
public import Silmaril.Project.CompilesTo.Thms

/-! `examples/compiles-to/branch/branch.c`, `O0`, `max2`, segment 0 (the entry, to line 4):
`FnData.segment_entry` (Core ↔ x86), and its composition with C ↔ Core (C ↔ x86). -/

namespace CompilesToExamples.Branch.O0

open Silmaril.Project.CompilesTo Silmaril.Project.Shapes.CompilesTo

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- **Core ↔ x86**, segment 0 of `max2`. -/
public theorem max2_seg_0 : Task.max2_seg_0 :=
  FnData.segment_entry max2 (xs := []) (sp := [(.rdi, 0xfffffffc, 4), (.rsi, 0xfffffff8, 8)])
    (hp := rfl) (hk0 := rfl) (hf0 := rfl) (hq := rfl) (hqk := rfl) (hbody := rfl) (hcr := rfl)
    (hkeys := by decide +kernel) (hnodup := by decide +kernel) (hroom := by decide)
    (hsig := by decide) (hdefs := by decide +kernel) (hslots := by decide +kernel)
    (hsp := by decide +kernel) (hdisp := by decide) (hpw := by decide) (hsp0 := by decide)
    (hqoff := rfl) (hmid := by decide) (hmid' := by decide) (hpush := by decide +kernel)
    (hmov := by decide +kernel) (hfr := by decide) (hfit := by decide) (hpts := by decide)
    (haddr := by decide)

/-- **C ↔ x86**, segment 0 of `max2`: C ↔ Core (function and point) and Core ↔ x86. -/
public theorem max2_seg_0_from_c : Task.max2_seg_0_from_c :=
  ⟨elaborates_max2, max2_point_0, max2_seg_0⟩

end CompilesToExamples.Branch.O0
