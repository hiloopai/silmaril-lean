module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Total
import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.VcB
import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.VcD
import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.VcE
import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.VcP
import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.VcA
import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.VcC

/-!
# `adler32_z`: the six segment VCs, and total correctness on `Open9`

`vcB`, `vcD`, `vcE`, `vcP` and the two `DO16` loops `vcA` (`0x80`, `VcA.lean`) and `vcC`
(`0x2e3`, `VcC.lean`) are proved; `total` assembles them. `total_of_vcAC` is the form with the
loop VCs as hypotheses.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z

open Silmaril.X86 (Word)
open Silmaril.X86
open Silmaril.X86.Ladder.ZlibChecksums

theorem vcB_holds : VcB 60 := fun c s hl hrip hI => vcB c s hl hrip hI
theorem vcD_holds : VcD 60 := fun c s hl hrip hI => vcD c s hl hrip hI
theorem vcE_holds : VcE 20 := fun c hP hl => vcE c hP hl
theorem vcP_holds : VcP 60 := fun c s hl hrip hI => vcP c s hl hrip hI

/-- **`adler32_z` is totally correct on `Open9`, given the VCs of the loops `0x80` and
`0x2e3`.** -/
theorem total_of_vcAC {KA KC : Nat} (hA : VcA KA) (hC : VcC KC) (entry : Word) :
    (adler32zContract entry).Total Open9.isa :=
  total_of hA vcB_holds hC vcD_holds vcE_holds vcP_holds entry

/-- **`adler32_z` is totally correct on `Open9`** (all six segment VCs proved). -/
theorem total (entry : Word) : (adler32zContract entry).Total Open9.isa :=
  total_of_vcAC vcA_holds vcC_holds entry

/-- The two loop VCs at the budget of `Task.adler32z_loops`. -/
theorem loops_holds : VcA 200 ∧ VcC 200 :=
  ⟨VcAt.mono vcA_holds (by decide), VcAt.mono vcC_holds (by decide)⟩

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
