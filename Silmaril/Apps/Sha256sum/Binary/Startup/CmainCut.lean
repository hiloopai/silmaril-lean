module

public import Silmaril.Apps.Sha256sum.Binary.Startup.Cuts

/-! # The strengthened end cut of `cmain`'s segment: `AtDigestEntryW`

`AtDigestEntry` (`digest_file`'s entry from the stdin-path call at `0x40419a`) together with
what `cmain`'s own frame holds at the call, for the segments after it (`csp = sp0 - 240`,
`cmain`'s `rsp`):

* `rbx = 0` (`do_check`, loaded at `0x4039aa`), `r12 = 0x406052` (the operand `"-"`) and
  `r14 = csp + 0x90` (`missing`, set at `0x40397c`), callee-saved registers `digest_file`'s
  prologue pushes;
* `cmain`'s locals: `ok = 1` at `csp + 0x2c`, the operand index `0` at `csp + 8` and the
  operand count `1` at `csp + 0x50` (`CMain.argLast` with `i = 0`);
* `binary = 0` (`0x409010`, stored at `0x40395b`).

Everything else `Wire.CMain` asks for is unchanged from launch outside `W2`, so it follows from
`LaunchFacts` and `AtDigestEntry.mem`.

Status: definitions, and the projection `AtDigestEntryW.toEntry` (VERIFIED).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup

open Silmaril.X86 (Word)
open Silmaril.X86.Ext (leBytes)
open Silmaril.Apps.Sha256sum.X86Sys (XState)

/-- **`digest_file`'s entry, with `cmain`'s frame** (`csp = sp0 - 240`). -/
structure AtDigestEntryW (c : Ctx) (s : XState) : Prop where
  entry : AtDigestEntry c s
  rbx : s.core.read .rbx = 0#64
  r12 : s.core.read .r12 = 0x406052#64
  r14 : s.core.read .r14 = c.sp0 - 240#64 + 0x90#64
  okFlag : s.memory.readWith .read (c.sp0 - 240#64 + 0x2c#64).toNat 4 = some (leBytes 1#64 4)
  argIdx : s.memory.readWith .read (c.sp0 - 240#64 + 8#64).toNat 8 = some (leBytes 0#64 8)
  argLast : s.memory.readWith .read (c.sp0 - 240#64 + 0x50#64).toNat 4 = some (leBytes 1#64 4)
  binary : s.memory.readWith .read 0x409010 4 = some (leBytes 0#64 4)

theorem AtDigestEntryW.toEntry {c : Ctx} {s : XState} (h : AtDigestEntryW c s) :
    AtDigestEntry c s := h.entry

end Silmaril.Apps.Sha256sum.Binary.Startup
