module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Statement
public import Silmaril.Process.LPS.Problems.Sha256Cli.NonVacuity
public import Silmaril.Apps.Sha256sum.Binary.Image

/-! # The GNU `sha256sum` LPS snapshot: image agreement and satisfiable hypotheses

* `segs_bytes` (VERIFIED): the LPS snapshot's segments (what `ELFImage.parse` extracts from
  the pinned file) are, base for base and byte for byte, the `PT_LOAD` contents that
  `Apps.Sha256sum.Binary.Image.image` transcribes. This is the image half of the launch
  correspondence between LPS and the `X86Sys` middle model.
* `brkSatisfiable`, `phdrsReadable` (VERIFIED): two of the three `ImageWf` checks.
* `admissible_exists` (VERIFIED modulo `EntryFetchable`, the decode of the entry instruction
  `xor %ebp,%ebp` at `0x401000`): every message has an admissible stdin-tier launch.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Process.LPS.Machines

set_option maxRecDepth 200000

theorem initPc_eq : snapshot.image.initPc = 0x401000 := by
  show (records.image file).initPc = _
  decide +kernel

theorem segs_shape : (records.image file).segments.map (fun s => (s.base, s.bytes.length)) =
    [(0x400000, 0x158), (0x401000, 0x43cb), (0x406000, 0x2010), (0x409010, 0xa140)] := by
  decide +kernel

/-- The LPS snapshot and the transcribed `X86Sys` image have the same segments. -/
theorem segs_bytes : (records.image file).segments.map (fun s => (s.base, s.bytes)) =
    Apps.Sha256sum.Binary.Image.image.segments.map (fun s => (s.vaddr, s.contents)) := by
  decide +kernel

theorem brkSatisfiable : imageBrkSatisfiable (records.image file).segments = true := by
  decide +kernel

theorem phdrsReadable :
    imagePhdrsReadable (records.image file).segments (records.image file).phdrs = true := by
  rw [Silmaril.Process.LPS.Problems.imagePhdrsReadable_eq_K]
  decide +kernel

/-- The remaining loader check: the entry instruction decodes in the initial image memory. -/
def EntryFetchable (oracle : Nat → X86FlagChoices.Choice) : Prop :=
  (machine oracle).entryFetchable (records.image file).segments (records.image file).initPc = true

theorem imageWf (oracle : Nat → X86FlagChoices.Choice) (fetchable : EntryFetchable oracle) :
    ImageWf (machine oracle) (records.image file) :=
  ⟨fetchable, phdrsReadable, brkSatisfiable⟩

/-- A valid stdin-tier LPS input whose standard input is `message` (argv `["a"]`). -/
def launchInput (message : List Byte) : ProcInput := Sha256Cli.launchInput message

/-- A valid LPS entry for the pinned image (stack at `0x7fffffffe000`, break `0x414000`). -/
def launchEntry : ExecEntry := ⟨0x7fffffffe000, 0x414000, 0x40000000, ⟨0, fun _ => 0⟩⟩

theorem launchInput_valid (message : List Byte) : X86Launch.ValidInput (launchInput message) :=
  X86Launch.Controls.input_valid

theorem launchEntry_valid (oracle : Nat → X86FlagChoices.Choice) (message : List Byte)
    (fetchable : EntryFetchable oracle) :
    X86Launch.ValidEntry (machine oracle) snapshot launchEntry (launchInput message) := by
  refine ⟨ELFImage.parsed_imageWf_validSnapshot parsed (imageWf oracle fetchable), ?_⟩
  have same : X86Launch.stackBytes snapshot.image launchEntry (launchInput message) =
      X86Launch.stackBytes snapshot.image launchEntry X86Launch.Controls.input := rfl
  rw [same]
  simp only [ValidBrk, snapshot, launchEntry]
  decide +kernel

/-- **Non-vacuity** of the LPS target, modulo `EntryFetchable`. -/
theorem admissible_exists (oracle : Nat → X86FlagChoices.Choice) (fetchable : EntryFetchable oracle)
    (message : List Byte) : ∃ en inp, Admissible oracle en inp message :=
  ⟨launchEntry, launchInput message, rfl, rfl, launchInput_valid message,
    launchEntry_valid oracle message fetchable⟩

end Silmaril.Process.LPS.Problems.GnuSha256sum
