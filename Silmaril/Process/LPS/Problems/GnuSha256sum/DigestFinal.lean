module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.DigestLoop
public import Silmaril.Apps.Sha256sum.Binary.Digest.FinalSpec

/-! # `sha_final`, as a `GStep` segment

From the padding cut point of the read loop (`DigestLoop.PadCut`: the last `read` returned 0, the
`struct sha` holds everything read from standard input) to the output stage: at `0x40310a` the
caller's 32-byte buffer holds **`SHA256.digest (stdinRead h)`**.

* `FinalPadCut e out`: `PadCut e`, the `sha_final` code region loaded, and the caller's buffer
  `out` (`Digest.OutBuf`: its address at `[sp + 0x10]`, writable and readable, apart from the
  frame).
* `OutCut e out`: `Ok`, and `Digest.AtOut e (stdinRead h) out` (the digest in `out`, the frame
  registers and both code regions of `digest_file` kept).

`finalSeg` (VERIFIED): `Seg domain (FinalPadCut e out) (OutCut e out)`, for every domain:
`Digest.final_digest` (retiring steps of the `Ext8` machine only, no system call) through the
bridge's `leads_of_reaches`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.X86Sys (XState)
open Silmaril.Apps.Sha256sum.Binary.Digest (Loop AtPad OutBuf AtOut)
open Silmaril.X86.Ext (Loaded)

/-- The padding, with the `sha_final` region loaded and the caller's digest buffer `out`. -/
def FinalPadCut (e : Loop) (out : Silmaril.X86.Word) : Cut := fun w message g h =>
  PadCut e w message g h ∧
    Loaded g.x.memory Apps.Sha256sum.Binary.Digest.Final.base
      Apps.Sha256sum.Binary.Digest.Final.code ∧
    OutBuf g.x.memory e.sp out

/-- The output stage: the digest of everything read is in `out`. -/
def OutCut (e : Loop) (out : Silmaril.X86.Word) : Cut := fun _ message g h =>
  Ok message g h ∧ AtOut e (stdinRead h) out g.x

/-- **VERIFIED. `sha_final`**, as a segment of the middle model: from `FinalPadCut` every
execution keeps `Ok` and reaches `OutCut`, the digest of the whole input in the buffer. -/
theorem finalSeg (domain : List Byte → Prop) (e : Loop) (out : Silmaril.X86.Word) :
    Seg domain (FinalPadCut e out) (OutCut e out) := by
  intro prog posix fs message g h _ ⟨⟨ok, hl0, pad⟩, hl, hout⟩
  have running := ok.1
  have hlv := ok.2.2.2.2.2
  obtain ⟨t, hrun, hlv', hpost⟩ :=
    Apps.Sha256sum.Binary.Digest.final_digest hlv hl hl0 pad hout
  have ok' : Ok message { g with x := t } h :=
    ⟨ok.1, ok.2.1, ok.2.2.1, ok.2.2.2.1, ok.2.2.2.2.1, hlv'⟩
  exact leads_of_reaches hrun running ok ⟨ok', hpost⟩

end Silmaril.Process.LPS.Problems.GnuSha256sum
