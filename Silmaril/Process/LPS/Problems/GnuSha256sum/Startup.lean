module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.SysTotal
public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameRuns

/-! # The startup of GNU `sha256sum` as `GStep` segments: the cut points

The startup runs with no system call (the measured stdin-path trace starts with
`read(0, …)`), so its segments are silent runs (`Silent.leads_of_reaches`) between cut points
whose history is still empty and whose kernel is still the launch kernel:

```
LaunchCut ──_start──▶ CmainEntryCut ──set_program_name──▶ OptParseCut ──cmain──▶ DigestEntryCut ──prologue──▶ loop head
```

* `CmainEntryCut`: `cmain`'s entry (`Startup.AtCmainEntry`, `0x4033f0`);
* `OptParseCut`: `cmain` after `set_program_name` (`Startup.AtOptParse`, `0x4034a6`);
* `DigestEntryCut`: `digest_file`'s entry from the stdin-path call at `0x40419a`, return
  address `0x40419f` (`Startup.AtDigestEntry`, `0x402de0`).

Both carry the launch context `Startup.Ctx` with `Startup.LaunchFacts` (what `Launch`
gives), so every later segment can read the image, the strings and the permissions of the
launch memory through the footprint (`Memory.WritesWithin`).

Status: everything proved here is VERIFIED (no `sorry`, no new axiom); `setProgNameSeg` takes
the `/` case of the base-name check (`SetName.SlashCase`) as a hypothesis.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.Binary.Startup (Ctx LaunchFacts AtCmainEntry AtOptParse AtDigestEntry)
open Silmaril.Apps.Sha256sum.X86Sys (XState)

/-- A silent startup cut: empty history, the launch kernel, running, and a state at `P` of a
launch context with its facts. -/
def StartCut (P : Ctx → XState → Prop) : Cut := fun w _ g h =>
  h = [] ∧ g.k = Silmaril.Apps.Sha256sum.Sys.KState.init w ∧ g.exited = none ∧
    ∃ c, LaunchFacts c ∧ P c g.x

/-- `cmain`'s entry (`0x4033f0`) from `_start`'s `call cmain` (`Startup.AtCmainEntry`). -/
def CmainEntryCut : Cut := StartCut AtCmainEntry

/-- `cmain` after `set_program_name` (`0x4034a6`). -/
def OptParseCut : Cut := StartCut AtOptParse

/-- **`digest_file`'s entry from the stdin-path call** (`0x402de0`; the call is at `0x40419a`,
return address `0x40419f`; operand `"-"` at `0x406052`). -/
def DigestEntryCut : Cut := StartCut AtDigestEntry

/-- A running, unfaulted state with an empty history is `Ok`. -/
theorem ok_nil {message : List Byte} {g : GS} (hex : g.exited = none)
    (hf : g.x.faulted = false) : Ok message g [] :=
  ⟨hex, by simp, by simp [stdinRead], by simp [out], .inl (by simp [out]), hf⟩

/-- A silent run between two startup cuts is a segment. -/
theorem startCut_seg {P Q : Ctx → XState → Prop}
    (run : ∀ c s, LaunchFacts c → P c s →
      ∃ t, Silmaril.Machine.Execution.Reaches Apps.Sha256sum.X86Sys.rStep8 s t ∧ Q c t)
    (faulted : ∀ c s, P c s → s.faulted = false) :
    Seg (fun _ => True) (StartCut P) (StartCut Q) := by
  intro prog posix fs message g h _ ⟨hh, hk, hex, c, hc, hp⟩
  subst hh
  obtain ⟨t, hr, ht⟩ := run c g.x hc hp
  exact leads_of_reaches hr hex (ok_nil hex (faulted c g.x hp)) ⟨rfl, hk, hex, c, hc, ht⟩

/-- **`set_program_name` as a segment** (VERIFIED from the `/` case `SetName.SlashCase`):
from `cmain`'s entry every execution keeps `Ok` and reaches `cmain` after
`set_program_name`. -/
theorem setProgNameSeg
    (hslash : ∀ c, LaunchFacts c → Silmaril.Apps.Sha256sum.Binary.Startup.SetName.SlashCase c) :
    Seg (fun _ => True) CmainEntryCut OptParseCut :=
  startCut_seg (fun c s hc h => Silmaril.Apps.Sha256sum.Binary.Startup.SetName.runs c hc
    (hslash c hc) s h) (fun _ _ h => h.faulted)

end Silmaril.Process.LPS.Problems.GnuSha256sum
