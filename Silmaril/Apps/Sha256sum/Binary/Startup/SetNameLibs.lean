module

public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameLibsK0
public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameLibsK1
public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameLibsK2
public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameLibsK3
public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameLibsK4
public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameLibsK5
public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameLibsK6
public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameSlashGlue

/-! # `set_program_name` (`sha256sum-min`): the `/` case, closed

* `vc_libs` (VERIFIED): the `"/.libs/"` loop-cut VC (cut `134`), by cases on the byte
  `k < 7` from `vc_libs_k0` .. `vc_libs_k6` (`SetNameLibsKN.lean`);
* `vc_libs_proved : VcLibs`, `vc_lt_proved : VcLt` (VERIFIED): the two loop-cut VCs in the
  shape `slashCase_of` takes (`vc_lt` is in `SetNameLt.lean`);
* `slashCase` (VERIFIED): `SlashCase` for every launch, with no hypothesis;
* `GnuSha256sum.setProgNameSegV` (VERIFIED): the `set_program_name` segment
  `CmainEntryCut → OptParseCut`, with no hypothesis.

Status: VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.SetName

open Silmaril.X86.Ext (Loaded)
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Apps.Sha256sum.Binary.Startup

/-- **VERIFIED. The `"/.libs/"` loop VC** (cut `134`): one iteration at byte `k`, a mismatch
to the join, a match to byte `k + 1` (or, at `k = 6`, to the `"lt-"` loop). -/
theorem vc_libs (c : Ctx) (hc : LaunchFacts c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory Main.base Main.code →
      s.core.rip = Main.base + BitVec.ofNat 64 134 → libsInv c s →
      LibsGoal c s := by
  intro s hlv hl hrip ⟨n, i, k, hn, hn0, hi, h6, hk, hrcx, hrax, hsp, hdi, hr11, hrsi, hr14, hww⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) with
    h | h | h | h | h | h | h
  · exact vc_libs_k0 c hc s hlv hl hrip hn hn0 hi h6 hrcx (hrax.trans h) hsp hdi hr11 hrsi hr14 hww
  · exact vc_libs_k1 c hc s hlv hl hrip hn hn0 hi h6 hrcx (hrax.trans h) hsp hdi hr11 hrsi hr14 hww
  · exact vc_libs_k2 c hc s hlv hl hrip hn hn0 hi h6 hrcx (hrax.trans h) hsp hdi hr11 hrsi hr14 hww
  · exact vc_libs_k3 c hc s hlv hl hrip hn hn0 hi h6 hrcx (hrax.trans h) hsp hdi hr11 hrsi hr14 hww
  · exact vc_libs_k4 c hc s hlv hl hrip hn hn0 hi h6 hrcx (hrax.trans h) hsp hdi hr11 hrsi hr14 hww
  · exact vc_libs_k5 c hc s hlv hl hrip hn hn0 hi h6 hrcx (hrax.trans h) hsp hdi hr11 hrsi hr14 hww
  · exact vc_libs_k6 c hc s hlv hl hrip hn hn0 hi h6 hrcx (hrax.trans h) hsp hdi hr11 hrsi hr14 hww

/-- **VERIFIED.** The `"/.libs/"` loop-cut VC, as `VcLibs`. -/
theorem vc_libs_proved : VcLibs := vc_libs

/-- **VERIFIED.** The `"lt-"` loop-cut VC, as `VcLt`. -/
theorem vc_lt_proved : VcLt := vc_lt

/-- **VERIFIED. The `/` case** of `set_program_name`, for every launch. -/
theorem slashCase : ∀ c, LaunchFacts c → SlashCase c := slashCase_of vc_libs_proved vc_lt_proved

end Silmaril.Apps.Sha256sum.Binary.Startup.SetName

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.Binary.Startup.SetName (vc_libs_proved vc_lt_proved)

/-- **`set_program_name` as a segment** (VERIFIED, no hypothesis): `setProgNameSeg'` with the
two loop-cut VCs proved. -/
theorem setProgNameSegV : Seg (fun _ => True) CmainEntryCut OptParseCut :=
  setProgNameSeg' vc_libs_proved vc_lt_proved

end Silmaril.Process.LPS.Problems.GnuSha256sum
