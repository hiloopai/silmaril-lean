module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Wire
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Prologue
public import Silmaril.Process.LPS.Problems.GnuSha256sum.StartupCmain
public import Silmaril.Process.LPS.Problems.GnuSha256sum.StartEntry
public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameLibs
public import Silmaril.Apps.Sha256sum.Stdout.HexSeg
public import Silmaril.Process.LPS.Problems.GnuSha256sum.FormatGlue
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Profile

/-! # GNU `sha256sum`: the release theorems

`Wire.OpenW` leaves two segments open, `startup` and `format`. This file composes each from
its pieces and states the five release theorems (and `profile-total`) with **no hypothesis**:

```
startup : LaunchCut ──startEntrySeg──▶ CmainEntryCut ──setProgNameSegV──▶ OptParseCut ──optParse_digestEntryW──▶ DigestEntryCutW ──prologueSeg──▶ AtLoopHeadW
format  : Digested ──FormatGlue.prefixSeg──▶ HexEntryCut ──hexSeg (hex_loop)──▶ HexExitCut ──suffix──▶ Formatted
```

* `_start → AtCmainEntry` (`0x401000 → 0x4033f0`): `startEntrySeg` (VERIFIED);
* `set_program_name`: `setProgNameSegV : AtCmainEntry → AtOptParse` (`0x4033f0 → 0x4034a6`,
  VERIFIED): `setProgNameSeg'` with the `/` case's loop-cut VCs `SetName.vc_libs_proved`
  (the `"/.libs/"` loop) and `SetName.vc_lt_proved` (the `"lt-"` loop);
* `cmain`: `optParse_digestEntryW : AtOptParse → AtDigestEntryW` (`0x4034a6 → 0x402de0`,
  VERIFIED);
* the prologue: `prologueSeg : AtDigestEntryW → AtLoopHeadW` (`0x402de0 → 0x402ef0`,
  VERIFIED);
* the prefix: `prefixSeg'` from `FormatGlue.prefixSeg` (`0x40310a → 0x404541`, VERIFIED)
  through the adapter `HexEntryCutP → HexEntryCut`;
* the hex loop: `Stdout.hexSeg` from `Stdout.hex_loop` (VERIFIED);
* the suffix: `Stdout.suffix` (`0x404605 → 0x40464d`, VERIFIED).

Status: VERIFIED (no `sorry`, no new axiom, no hypothesis).
-/

@[expose] public section

namespace Silmaril.Process.LPS.Problems.GnuSha256sum.Close

open Silmaril.Process.LPS.Problems.GnuSha256sum
open Silmaril.Process.LPS.Problems.GnuSha256sum.Wire
open Silmaril.Apps.Sha256sum.Stdout (HexEntryCut HexExitCut hexSeg suffix)

/-- The whole stdin tier. -/
abbrev All : List Byte → Prop := fun _ => True

/-- **The startup segment** (VERIFIED): `startEntrySeg` ; `setProgNameSegV` ;
`optParse_digestEntryW` ; `prologueSeg`. -/
theorem startup : Seg All LaunchCut AtLoopHeadW :=
  startEntrySeg.trans (setProgNameSegV.trans
    ((optParse_digestEntryW All).trans (prologueSeg All)))

/-- **The prefix of the format segment into `HexEntryCut`** (VERIFIED): `FormatGlue.prefixSeg`
ends at `FormatGlue.HexEntryCutP`, which has the same fields. -/
theorem prefixSeg' : Seg All Digested HexEntryCut :=
  fun prog posix fs message g h member start =>
    (FormatGlue.prefixSeg All prog posix fs message g h member start).trans
      fun _ _ ⟨d, buf, emitted, a⟩ => .done (by
        unfold HexEntryCut
        exact ⟨buf, emitted, d, ⟨a.ok, a.rip, a.code, a.fd0, a.fd1, a.fd2, a.entry, a.rbx, a.rbp,
          a.r12, a.r13, a.mem, a.obuf, a.co, a.read, a.answer⟩⟩)

/-- **The format segment** (VERIFIED): prefix ; hex loop ; suffix. -/
theorem formatSeg : Seg All Digested Formatted :=
  prefixSeg'.trans ((hexSeg All).trans (suffix All))

/-- `Wire.OpenW` (VERIFIED). -/
theorem openW_close : OpenW :=
  ⟨startup, formatSeg⟩

/-! ## The release theorems -/

/-- **`sys-total`** (VERIFIED). -/
@[solves "sha256/gnu-sha256sum-x86-64/sys-total"]
theorem sysTotal_close : Registry.sysTotal :=
  sysTotal_of_W openW_close

/-- **`lps-total`** (VERIFIED). -/
@[solves "sha256/gnu-sha256sum-x86-64/lps-total"]
theorem lpsTotal_close : Registry.lpsTotal :=
  lpsTotal_of_W openW_close

/-- **`lps-bounded-1024`** (VERIFIED). -/
@[solves "sha256/gnu-sha256sum-x86-64/lps-bounded-1024"]
theorem lpsBounded_close : Registry.lpsBounded :=
  lpsBounded_of_W openW_close

/-- **`lps-partial`** (VERIFIED). -/
@[solves "sha256/gnu-sha256sum-x86-64/lps-partial"]
theorem lpsPartial_close : Registry.lpsPartial :=
  lpsPartial_of_W openW_close

/-- **`agree-sha256-cli`** (VERIFIED). -/
@[solves "sha256/gnu-sha256sum-x86-64/agree-sha256-cli"]
theorem agree_close : Registry.agree :=
  agree_of_W openW_close

/-- **`profile-total`** (the parity `ProfileProblem` statements, `GnuSha256sum.Parity`),
VERIFIED through `lps-total`. -/
@[solves "sha256/gnu-sha256sum-x86-64/profile-total"]
theorem profileTotal_close : Parity.profileTotal :=
  Parity.profileTotal_link ⟨lpsTotal_close, trivial⟩

end Silmaril.Process.LPS.Problems.GnuSha256sum.Close
