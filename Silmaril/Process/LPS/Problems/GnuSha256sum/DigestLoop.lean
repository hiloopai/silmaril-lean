module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Silent
public import Silmaril.Apps.Sha256sum.Binary.Digest.Spec

/-! # The hashing part of the read loop, as a `GStep` segment

The cut points of one iteration of `digest_file`'s read loop (`Binary.Digest.Spec`), as `Cut`s
of the middle model, with the history: the bytes consumed so far are **everything read from
standard input** (`stdinRead h`), and the `struct sha` has absorbed them (`Digest.Absorbed`:
its chaining value is the SHA-256 fold over their full blocks, `Absorbed.stream`).

* `AfterReadCut e`: `read` has just returned a chunk; the struct holds what was read before it.
* `HeadCut e`: at the loop head, the struct holds everything read.
* `PadCut e`: at the padding, the struct holds everything read (the last `read` returned 0).

`updateSeg` (VERIFIED): `Seg domain (AfterReadCut e) (HeadCut e ∨ PadCut e)`, for every
domain: `Digest.update_absorbs` (the `sha_update` proof, retiring steps only) through the
bridge's `leads_of_reaches` (silent runs are `Leads` segments of `GStep`, for any `r11`).
What remains of `ReadLoopSegment` is the system-call part of an iteration: `HeadCut` to
`AfterReadCut` across `read(0, iobuf, 32768)` (the `read` wrapper at `0x401010`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.X86Sys (XState)
open Silmaril.Apps.Sha256sum.Binary.Digest (Loop AfterRead AtHead AtPad)
open Silmaril.X86.Ext (Loaded)

/-- `read` has just returned `chunk`; the struct holds everything read before it. -/
def AfterReadCut (e : Loop) : Cut := fun _ message g h =>
  Ok message g h ∧ Loaded g.x.memory Apps.Sha256sum.Binary.Digest.base
    Apps.Sha256sum.Binary.Digest.code ∧
    ∃ consumed chunk, stdinRead h = consumed ++ chunk ∧ AfterRead e consumed chunk g.x

/-- The loop head: the struct holds everything read so far. -/
def HeadCut (e : Loop) : Cut := fun _ message g h =>
  Ok message g h ∧ Loaded g.x.memory Apps.Sha256sum.Binary.Digest.base
    Apps.Sha256sum.Binary.Digest.code ∧ AtHead e (stdinRead h) g.x

/-- The padding: the struct holds everything read so far. -/
def PadCut (e : Loop) : Cut := fun _ message g h =>
  Ok message g h ∧ Loaded g.x.memory Apps.Sha256sum.Binary.Digest.base
    Apps.Sha256sum.Binary.Digest.code ∧ AtPad e (stdinRead h) g.x

/-- **VERIFIED. The hashing part of one read-loop iteration**, as a segment of the middle
model: from `AfterReadCut` every execution keeps `Ok` and reaches `HeadCut` or `PadCut`. -/
theorem updateSeg (domain : List Byte → Prop) (e : Loop) :
    Seg domain (AfterReadCut e) (fun w m g h => HeadCut e w m g h ∨ PadCut e w m g h) := by
  intro prog posix fs message g h _ ⟨ok, hl, consumed, chunk, hread, after⟩
  have running := ok.1
  have hlv := ok.2.2.2.2.2
  obtain ⟨t, hrun, hlv', hl', hpost⟩ :=
    Apps.Sha256sum.Binary.Digest.update_absorbs hlv hl after
  have hrun8 : Silmaril.Machine.Execution.Reaches retStep g.x t :=
    Apps.Sha256sum.X86Sys.reaches_rStep8 hrun
  have ok' : Ok message { g with x := t } h :=
    ⟨ok.1, ok.2.1, ok.2.2.1, ok.2.2.2.1, ok.2.2.2.2.1, hlv'⟩
  refine leads_of_reaches hrun8 running ok ?_
  rcases hpost with ⟨head, _⟩ | ⟨rfl, pad⟩
  · exact .inl ⟨ok', hl', by rw [hread]; exact head⟩
  · exact .inr ⟨ok', hl', by rw [hread, List.append_nil]; exact pad⟩

end Silmaril.Process.LPS.Problems.GnuSha256sum
