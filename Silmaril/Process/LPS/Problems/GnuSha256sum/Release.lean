module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Registry
public import Silmaril.Process.LPS.Problems.GnuSha256sum.ReadEof
public import Silmaril.Process.LPS.Problems.GnuSha256sum.ReadLoop

/-! # GNU `sha256sum`: the LPS tiers from the remaining segments (integration)

`lps-bridge` is solved (`Registry.lpsBridge_solution`), so `lps-total` and the weaker tiers
follow from `sys-total`, and `sys-total` from its segments (`SysModel.sysTotalOn_of_segments`).
This file states the LPS tiers with the segments that were open as hypotheses (`Open`;
superseded by `Wire.OpenW`, see `Open`):

* `startup`: launch to the read loop's head (`ReadLoop.AtLoopHead`: the `struct sha`
  initialised, descriptor 0, the kernel's stdin the whole message);
* `final`, `format`, `exit`: `sha_final` from the padding (`ReadLoop.AtLoopPad`), the
  68-byte record, and `close(0)`/`out_flush`/`close(1)`/`close(2)`/`exit_group(0)`.

Discharged: `lps-bridge`, the read loop (`ReadLoop.readLoopSeg`, `gnu-r3-readloop`; also
`readLoop_stdin` through the integrator's `SysTotal.readLoop` with `readCall_solved`,
`keepsJ_stdin` and `eofStep`), and every composition. `headK_iff`/`padK_iff`: the two forms
of the loop's cuts agree.

Status: everything in this file is VERIFIED (no `sorry`, no new axiom); the hypotheses are
hypotheses, not axioms.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum.Release

open Silmaril.Process.LPS.Problems.GnuSha256sum
open Silmaril.Apps.Sha256sum.Binary.Digest (Loop)

/-! ## The two forms of the read loop's cuts agree -/

theorem headK_iff (e : Loop) (w : Apps.Sha256sum.World) (message : List Byte) (g : GS)
    (h : List Ev) : HeadK e w message g h ↔ HeadJ StdinJ e w message g h :=
  ⟨fun ⟨hd, k, fd⟩ => ⟨hd, fd, k.fd0, k.fd1, k.fd2, k.stdin, k.quiet⟩,
    fun ⟨hd, fd, f0, f1, f2, st, q⟩ => ⟨hd, ⟨f0, f1, f2, st, q⟩, fd⟩⟩

theorem padK_iff (w : Apps.Sha256sum.World) (message : List Byte) (g : GS) (h : List Ev) :
    AtLoopPad w message g h ↔ PadJ StdinJ w message g h :=
  ⟨fun ⟨e, pd, k, fd⟩ => ⟨e, pd, fd, k.fd0, k.fd1, k.fd2, k.stdin, k.quiet⟩,
    fun ⟨e, pd, fd, f0, f1, f2, st, q⟩ => ⟨e, pd, ⟨f0, f1, f2, st, q⟩, fd⟩⟩

/-- **The system-call half of the read loop** (VERIFIED: `ReadLoop.readCall_stdin`,
`gnu-r3-readloop`). -/
theorem readCall_solved (domain : List Byte → Prop) : ReadCall domain StdinJ :=
  fun e prog posix fs message g h _ head j => readCall_stdin e prog posix fs message g h head j

/-- **The read loop, in the integrator's form** (VERIFIED twice: `SysTotal.readLoop` from
`readCall_solved`, `keepsJ_stdin`, `eofStep`; and `ReadLoop.readLoopSeg`). -/
theorem readLoop_stdin (domain : List Byte → Prop) :
    Seg domain (fun w message g h => ∃ e, HeadJ StdinJ e w message g h) (PadJ StdinJ) :=
  readLoop (readCall_solved domain) keepsJ_stdin eofStep

/-! ## What is still open -/

/-- The segments of `sys-total` that are still open: the startup to the read loop's head
(`ReadLoop.AtLoopHead`), and from its padding (`ReadLoop.AtLoopPad`) the final, format and
exit segments, for a choice of the two inner cut points of the tail.

**Superseded by `Wire.OpenW`.** `final` cannot be proved from `AtLoopPad`, which records
neither end of file (`Done` needs `stdinRead h = message`) nor `digest_file`'s caller, so this
structure is not satisfiable as stated. `Wire.OpenW` uses the strengthened cuts
`AtLoopHeadW`/`AtLoopPadW`, proves `final` (`Wire.finalW`), and leaves startup, format and
exit open. -/
structure Open (Digested Formatted : Cut) : Prop where
  startup : Seg (fun _ => True) LaunchCut AtLoopHead
  final : Seg (fun _ => True) AtLoopPad Digested
  format : Seg (fun _ => True) Digested Formatted
  exit : Seg (fun _ => True) Formatted DoneCut

variable {Digested Formatted : Cut}

/-- **`sys-total` from the open segments** (VERIFIED; the read loop by
`ReadLoop.readLoopSeg`). -/
theorem sysTotal_of (o : Open Digested Formatted) : Registry.sysTotal :=
  sysTotalOn_of_segments o.startup (readLoopSeg _) o.final o.format o.exit

/-- **`lps-total` from the open segments** (VERIFIED; `lps-bridge` is solved). -/
theorem lpsTotal_of (o : Open Digested Formatted) : Registry.lpsTotal :=
  Registry.lpsTotal_of (sysTotal_of o) Registry.lpsBridge_solution

/-- `lps-bounded-1024` from the open segments (VERIFIED). -/
theorem lpsBounded_of (o : Open Digested Formatted) : Registry.lpsBounded :=
  Registry.lpsBounded_link ⟨lpsTotal_of o, trivial⟩

/-- `lps-partial` from the open segments (VERIFIED). -/
theorem lpsPartial_of (o : Open Digested Formatted) : Registry.lpsPartial :=
  Registry.lpsPartial_link ⟨lpsTotal_of o, trivial⟩

/-- `agree-sha256-cli` from the open segments (VERIFIED; the filter's `lps-total` is
solved). -/
theorem agree_of (o : Open Digested Formatted) : Registry.agree :=
  Registry.agree_of_lpsTotal (lpsTotal_of o)

end Silmaril.Process.LPS.Problems.GnuSha256sum.Release
