module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Statement
public import Silmaril.Process.LPS.Problems.Basic
public import Silmaril.Process.LPS.Machines.X86LaunchControls

/-! # The LPS hypotheses of the `sha256` target are satisfiable

`Admissible oracle en inp message` (finite stdin, `ValidInput`, `ValidEntry` for the pinned
snapshot) has a witness on every message once the entry instruction is known to be fetchable
in the initial image memory (`EntryFetchable`). Everything else is proved here (VERIFIED):
the parsed records (`Elf.parsed`), the readable program-header table, the satisfiable break,
a valid input (the existing x86 launch control's input with the message as stdin) and a valid
entry (stack at `0x7fffffffe000`, break `0x402000`, mmap base `0x40000000`).

`EntryFetchable` (a `decode` of `call 0x400100`, `e8 0b 00 00 00`, at `0x4000f0` in
`initialMemory`) is proved in `Fetchable.lean` with the installer lemmas, which gives the
unconditional `Fetchable.admissible`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS.Machines

set_option maxRecDepth 100000

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

/-- A valid LPS input whose standard input is `message`. -/
def launchInput (message : List Byte) : ProcInput :=
  { X86Launch.Controls.input with stdin := InputStream.ofList message }

/-- A valid LPS entry for the pinned image. -/
def launchEntry : ExecEntry := ⟨0x7fffffffe000, 0x402000, 0x40000000, ⟨0, fun _ => 0⟩⟩

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
  ⟨launchEntry, launchInput message, rfl, launchInput_valid message,
    launchEntry_valid oracle message fetchable⟩

end Silmaril.Process.LPS.Problems.Sha256Cli
