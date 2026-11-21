module

public import Silmaril.Elf.Staged.Pinned.HelloGcc.Regions.Thms
public import Silmaril.Machine.Region.X86.CFG.Thms

@[expose] public section
namespace Silmaril.Elf.Staged.Pinned.HelloGcc.Regions.Examples
open Silmaril.Machine.Region.X86.CFG

/-- Omitting a real conditional edge fails intrinsic certification. -/
theorem missing_edge_rejected : ¬ missingFallthrough.Valid := by decide +kernel

/-- Permuting exits changes no extensional validity. -/
theorem exit_order_irrelevant : ({ compareRow with exits := [0x10c3, 0x10d8] } : Row).Valid := by
  decide +kernel

/-- The same listing cannot certify modified bytes. -/
theorem tampered_bytes_rejected :
    ¬ ({ compareRow with code := ⟨0x10be, [0x90, 0x39, 0xf8, 0x74, 0x15]⟩ } : Row).Valid := by
  decide +kernel

/-- A return is not an empty normal-target proof in the direct subset. -/
theorem return_rejected : ¬ (Row.mk ⟨0, [0xc3]⟩ 1 [⟨0, .ret, 1⟩] 0 [] []).Valid := by
  decide +kernel

/-- Corpus denominator: two chosen windows, four instructions and fourteen
bytes, within the pinned file's 265-byte .text. No whole-file coverage claim. -/
theorem selected_coverage :
    [compareRow, tailRow].length = 2 ∧
    compareRow.listing.length + tailRow.listing.length = 4 ∧
    compareCode.length + tailCode.length = 14 ∧ sh16.size = 265 := by decide

end Silmaril.Elf.Staged.Pinned.HelloGcc.Regions.Examples
