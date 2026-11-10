module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Main

/-!
# `adler32_z` below 16 bytes: unconditional

For `len < 16` (and the null buffer, `len ≠ 1`) no execution reaches the two `DO16` loop heads
with their invariants (`vcA_short`, `vcC_short`), so the proved VCs alone give the System V
contract: `total_short` needs no Task.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Short

open Silmaril.X86 (Word)
open Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
open Silmaril.X86
open Silmaril.X86.Ladder.ZlibChecksums

/-- **`adler32_z` is totally correct on `Open9` for `len < 16`** (no Task). -/
theorem total_short (entry : Word) : (adler32zShortContract entry).Total Open9.isa := by
  intro m0 _ hab ⟨he, hn⟩
  obtain ⟨t, hr, res⟩ := run_of (vcA_short (c := ⟨entry, m0⟩) hn 0) vcB_holds
    (vcC_short (c := ⟨entry, m0⟩) hn 0) vcD_holds vcE_holds vcP_holds hab he
  exact ⟨t, hr, res.silent, res.abi, res.frame, res.post⟩

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Short
