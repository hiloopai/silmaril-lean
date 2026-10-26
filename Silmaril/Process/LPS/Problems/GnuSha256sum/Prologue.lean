module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Wire
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Startup
public import Silmaril.Apps.Sha256sum.Binary.Startup.CmainCut
public import Silmaril.Apps.Sha256sum.Binary.Startup.PrologueRun

/-! # The prologue of `digest_file` as a `GStep` segment

From `digest_file`'s entry on the stdin path (`DigestEntryCutW`: `0x402de0`, operand `"-"`,
return address `0x40419f`, `cmain`'s frame) to the read loop's head with the caller's state
(`Wire.AtLoopHeadW`). The prologue makes no system call, so the segment is a silent run
(`Startup.Prologue.prologue_reaches`, retiring steps of the `Ext8` machine) through
`leads_of_reaches`. At the head:

* `HeadK`: `Ok` (empty history), the read loop's code, `Digest.AtHead e []` (`sha_init`'s
  state, nothing absorbed), the launch kernel (`StdinK`: descriptors 0/1/2, standard input the
  whole message, nothing written), descriptor `0`;
* `Wire.Entry e`: `Caller e` (the six saved registers with `rbx = 0`, `r12 = "-"`,
  `r14 = cmain's rsp + 0x90`, the return address `0x40419f`, `rbp = r13 = 0`, `CMain` at
  `cmain`'s `rsp` via `Prologue.cmain_of_entry`, with `have_read_stdin = 1` set here) and the
  digest buffer slot `[sp + 0x10] = bin e`.

`prologueSegR` (VERIFIED) is the segment from `DigestEntryCutR` (`DigestEntryCutW` with
`cmain`'s `r14 = rsp + 0x90` stated separately); `prologueSeg` (VERIFIED) is the segment from
`DigestEntryCutW`, whose `AtDigestEntryW` records `r14`.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.Binary.Startup (Ctx LaunchFacts AtDigestEntryW W2 W1)
open Silmaril.Apps.Sha256sum.Binary.Startup.Prologue (post PW WW loopOf prologue_reaches
  atHead_of_post readBytes_of_loadN8 readBytes_of_loadN ww_launch WP e448 cmain_of_entry)
open Silmaril.Apps.Sha256sum.X86Sys (XState)
open Silmaril.X86 (Word)
open Silmaril.X86.Ext (loadN leBytes)
open Silmaril.Process (Memory)

/-- `digest_file`'s entry with `cmain`'s frame and `r14 = rsp + 0x90`. -/
def DigestEntryCutR : Cut :=
  StartCut fun c s => AtDigestEntryW c s ∧ s.core.read .r14 = c.sp0 - 240#64 + 0x90#64

theorem readWith_of_loadN8 {m : Memory} {a v : Word} (h : loadN m a 8 = some v) :
    m.readWith .read a.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v]) := by
  rw [← Silmaril.X86.Ext.leBytes_eight]; exact readBytes_of_loadN8 h

set_option maxRecDepth 200000 in
/-- **VERIFIED. `Wire.Entry` after the prologue.** -/
theorem entry_of_post {c : Ctx} {s t : XState} (lf : LaunchFacts c) (en : AtDigestEntryW c s)
    (hr14 : s.core.read .r14 = c.sp0 - 240#64 + 0x90#64) (hp : post c s t) :
    Wire.Entry (loopOf c t) := by
  have ww := ww_launch en.entry hp
  have hlo := lf.spLo
  have hhi := lf.spHi
  have e : (loopOf c t).sp.toNat = c.sp0.toNat - 448 := e448 lf
  obtain ⟨-, -, -, -, -, hout, -, -, -, -, -, -, sbx, sbp, s12, s13, s14, s15, sret, hstd,
    hww, -⟩ := hp
  have q : ∀ a b : Nat, a ≤ 448 → b ≤ a →
      c.sp0 - BitVec.ofNat 64 a + BitVec.ofNat 64 b = c.sp0 - BitVec.ofNat 64 (a - b) := by
    intro a b ha hab
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  have hstdin : t.memory.readWith .read 0x40a0a0 4 = some (leBytes 1#64 4) := by
    have h := readBytes_of_loadN (k := 4) (by decide) hstd
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    exact h
  have hcm := cmain_of_entry lf en hww.ww hstdin
  have hcsp : (loopOf c t).sp + 0xd0#64 = c.sp0 - 240#64 := q 448 0xd0 (by omega) (by omega)
  have hdash : t.memory.readWith .read 0x406052 2 = some [0x2d#8, 0#8] := by
    rw [ww.readWith]
    · exact Silmaril.Apps.Sha256sum.Binary.Startup.Prologue.seg2_rd lf.mapped 0x52 2 (by decide)
        (by decide) (by decide +kernel)
    · intro o ho hin; simp only [WP, W2, W1, PW] at hin; omega
  refine ⟨⟨⟨by rw [e]; omega, by rw [e]; omega⟩, rfl, ?_, ?_, ⟨s.core.read .rbp, ?_⟩, ⟨?_, hdash⟩,
    ⟨s.core.read .r13, ?_⟩, ?_, ⟨s.core.read .r15, ?_⟩, ?_, by rw [hcsp]; exact hcm⟩, ?_⟩
  · rw [e]
    exact (ww.permitted_iff _ _ _).mpr (Silmaril.X86.Ext.Memory.Permitted.sub
      (lf.rw .read (by decide)) (by decide) (by omega) (by omega))
  · rw [show (loopOf c t).sp + 0x98#64 = c.sp0 - 296#64 from q 448 0x98 (by omega) (by omega), ← en.rbx]
    exact readWith_of_loadN8 sbx
  · rw [show (loopOf c t).sp + 0xa0#64 = c.sp0 - 288#64 from q 448 0xa0 (by omega) (by omega)]
    exact readWith_of_loadN8 sbp
  · rw [show (loopOf c t).sp + 0xa8#64 = c.sp0 - 280#64 from q 448 0xa8 (by omega) (by omega), ← en.r12]
    exact readWith_of_loadN8 s12
  · rw [show (loopOf c t).sp + 0xb0#64 = c.sp0 - 272#64 from q 448 0xb0 (by omega) (by omega)]
    exact readWith_of_loadN8 s13
  · rw [show (loopOf c t).sp + 0xb8#64 = c.sp0 - 264#64 from q 448 0xb8 (by omega) (by omega), hcsp, ← hr14]
    exact readWith_of_loadN8 s14
  · rw [show (loopOf c t).sp + 0xc0#64 = c.sp0 - 256#64 from q 448 0xc0 (by omega) (by omega)]
    exact readWith_of_loadN8 s15
  · rw [show (loopOf c t).sp + 0xc8#64 = c.sp0 - 248#64 from q 448 0xc8 (by omega) (by omega)]
    exact readWith_of_loadN8 sret
  · show loadN t.memory (c.sp0 - 448#64 + 16#64) 8 = some ((loopOf c t).sp + 0xd0#64 + 0x70#64)
    rw [hout, en.entry.rsi, hcsp]

/-- The launch kernel of a stdin-tier world, before any event. -/
theorem stdinK_init {prog : List Byte} {posix : Bool}
    {fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult} {message : List Byte} {g : GS}
    (hk : g.k = Apps.Sha256sum.Sys.KState.init (world [prog] posix fs message)) :
    StdinK message g [] := by
  refine ⟨?_, ?_, ?_, ?_, by simp [out]⟩ <;>
    simp [hk, Apps.Sha256sum.Sys.KState.init, world, stdinRead]

/-- **VERIFIED. The prologue of `digest_file`**, as a segment of the middle model: from
`digest_file`'s entry on the stdin path (with `cmain`'s frame and `r14`), every execution keeps
`Ok` and reaches the read loop's head with the caller's state (`Wire.AtLoopHeadW`). -/
theorem prologueSegR (domain : List Byte → Prop) : Seg domain DigestEntryCutR Wire.AtLoopHeadW := by
  intro prog posix fs message g h _ ⟨hh, hk, hex, c, lf, en, hr14⟩
  subst hh
  obtain ⟨t, hrun, hlv, hrip, hp⟩ := prologue_reaches lf en.entry
  obtain ⟨head, hl⟩ := atHead_of_post lf en.entry hp hrip
  refine leads_of_reaches hrun hex (ok_nil hex en.entry.faulted) ⟨loopOf c t,
    ⟨⟨ok_nil hex hlv, hl, head⟩, stdinK_init hk, rfl⟩, entry_of_post lf en hr14 hp⟩

/-- **VERIFIED. The prologue segment** from `DigestEntryCutW = StartCut AtDigestEntryW`
(`AtDigestEntryW` records `r14 = rsp + 0x90`). Stated with the cut's definition, so that this
file does not import `cmain`'s segment. -/
theorem prologueSeg (domain : List Byte → Prop) :
    Seg domain (StartCut AtDigestEntryW) Wire.AtLoopHeadW :=
  fun prog posix fs message g h member ⟨hh, hk, hex, c, lf, en⟩ =>
    prologueSegR domain prog posix fs message g h member ⟨hh, hk, hex, c, lf, en, en.r14⟩

end Silmaril.Process.LPS.Problems.GnuSha256sum
