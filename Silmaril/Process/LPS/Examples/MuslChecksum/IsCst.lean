module

-- GENERATED FILE by tools/elf-ast --iscst. DO NOT EDIT.
-- Input SHA256: 0ef7a89e9e1e07386fb608d06255b5523081ff9a48e0aa4c69a42e2311ed4ad0; 16256 bytes; 42 blocks; 4 segments.
-- Every theorem below is checked by the kernel; the segment table is data.
public import Silmaril.Process.LPS.Examples.MuslChecksum.Cst
public import Silmaril.Process.LPS.Examples.MuslChecksum.Bytes
public import Silmaril.Formats.ELF.Cst.IsCstCommand

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace «Silmaril».«Process».«LPS».«Examples».«MuslChecksum».«IsCst»

open Silmaril Silmaril.Formats.ELF

-- The file's bytes, as the chunk literals of `Silmaril.Process.LPS.Examples.MuslChecksum.Bytes.original`.
binary_image image of_literal Silmaril.Process.LPS.Examples.MuslChecksum.Bytes.original

-- The raw literal of every raw block of the CST.
cst_literals lits of Silmaril.Process.LPS.Examples.MuslChecksum.Cst.cst

/-- Segments: first block, end block, first byte, end byte, SHA-256 of those bytes. -/
def segments : List (Nat × Nat × Nat × Nat × String) := [
  (0, 8, 0, 4096, "0f23b33ad75c5ba15fecad5dee2fa6c8efc8542d7ce6e885613f6e31c6d768ae"),
  (8, 13, 4096, 8192, "6b024ea4d0080d77bb649da6dbc3545724616fbb31080f96866762ecd7492398"),
  (13, 20, 8192, 12288, "a0119088cdc83766f2a88ca71d7f8495153e9e342040046ba48ee0b6c553ca66"),
  (20, 42, 12288, 16256, "119b10d7ed47edceaaae5661a27e079300d286384fcd71268ad9a226b39398b1")
]

theorem start : Silmaril.Process.LPS.Examples.MuslChecksum.Cst.cst.startOK image = true := by decide +kernel

theorem segment0 : Silmaril.Process.LPS.Examples.MuslChecksum.Cst.cst.segmentOK image lits 0 8 = true := by decide +kernel
theorem segment1 : Silmaril.Process.LPS.Examples.MuslChecksum.Cst.cst.segmentOK image lits 8 13 = true := by decide +kernel
theorem segment2 : Silmaril.Process.LPS.Examples.MuslChecksum.Cst.cst.segmentOK image lits 13 20 = true := by decide +kernel
theorem segment3 : Silmaril.Process.LPS.Examples.MuslChecksum.Cst.cst.segmentOK image lits 20 42 = true := by decide +kernel

/-- The CST is the file: ranged checks over all 42 blocks. -/
theorem isCST : Silmaril.Process.LPS.Examples.MuslChecksum.Cst.cst.IsCST image lits = true :=
  Cst.File.isCST_of_segment start (by decide +kernel) (Cst.File.segmentOK_trans (by decide) (by decide) (Cst.File.segmentOK_trans (by decide) (by decide) (Cst.File.segmentOK_trans (by decide) (by decide) segment0 segment1) segment2) segment3)

theorem bytes_eq : Silmaril.Process.LPS.Examples.MuslChecksum.Cst.cst.bytes = some Silmaril.Process.LPS.Examples.MuslChecksum.Bytes.original :=
  (Cst.File.isCST_sound isCST lits_match).trans (congrArg some image.bits_eq_source)

theorem lossless : Silmaril.Process.LPS.Examples.MuslChecksum.Cst.cst.Lossless Silmaril.Process.LPS.Examples.MuslChecksum.Bytes.original := bytes_eq

theorem layoutWellFormed : Silmaril.Process.LPS.Examples.MuslChecksum.Cst.cst.LayoutWellFormed :=
  Cst.File.isCST_layoutWellFormed isCST lits_match

end «Silmaril».«Process».«LPS».«Examples».«MuslChecksum».«IsCst»
