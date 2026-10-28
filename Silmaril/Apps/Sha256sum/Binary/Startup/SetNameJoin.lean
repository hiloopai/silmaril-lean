module

public import Silmaril.Apps.Sha256sum.Binary.Startup.SetName
public import Silmaril.Apps.Sha256sum.Basic

/-! # The join cut of `set_program_name` (`0x403486`, listing offset 150)

Every path from the scan exit (`0x403444`) through the `"/.libs/"` and `"lt-"` checks reaches
`0x403486` with `r8` pointing at the program name: `argv[0]` with the prefix that
gnulib's `set_program_name` strips (`progName`, which always returns a suffix of `argv[0]`)
skipped, and the registers of `common` unchanged.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.SetName

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.Apps.Sha256sum.X86Sys

/-- The first `n` bytes of `argv[0]` (its string, without the NUL), as `Bytes`. -/
def argBytes (c : Ctx) (n : Nat) : Bytes := (c.arg.take n).map UInt8.ofBitVec

/-- The post at the join `0x403486`: `n` is the first NUL of `argv[0]`, `r8` is the program
name `progName argv[0]` (a suffix of `argv[0]`, so `argv0 + (n - its length)`). -/
def JoinPost (c : Ctx) (t : XState) : Prop :=
  ∃ n, n < c.arg.length ∧ c.arg[n]! = 0 ∧ (∀ q, q < n → c.arg[q]! ≠ 0) ∧
    t.core.read .r8 = c.argv0 + BitVec.ofNat 64 (n - (progName (argBytes c n)).length) ∧
    common c t

end Silmaril.Apps.Sha256sum.Binary.Startup.SetName
