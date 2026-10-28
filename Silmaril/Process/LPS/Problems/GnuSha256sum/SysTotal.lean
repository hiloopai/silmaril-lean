module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.SysGlue
public import Silmaril.Process.LPS.Problems.GnuSha256sum.DigestLoop

/-! # `sys-total` from its segments (integration)

The middle statement `SysTotalOn` assembled from the segment results of the provers, with
the segments that have not landed yet taken as **named hypotheses** (no `sorry`). As each
lands, its hypothesis is discharged here.

```
Launch ──startup──▶ HeadJ J ──readLoop──▶ PadJ J ──tail (final, format, exit)──▶ Done
```

* `HeadJ J e` / `PadJ J`: the loop head and the padding of `digest_file` (`DigestLoop.HeadCut`,
  `PadCut`: the `struct sha` has absorbed everything read so far), with an extra invariant
  `J` chosen by the read-loop prover.
* `loop_of_iter` (generic, VERIFIED): a loop of `read` calls leads from its head to its exit
  if each call reads exactly what it reports and a nonempty chunk returns to the head; the
  measure is the number of message bytes not yet read.
* **The read loop** (`readLoop`, VERIFIED from three hypotheses, one of them discharged):
  `ReadCall J` (the system-call half: `read(0, iobuf, 32768)` from the loop head back to
  `0x402f06`, keeping a prover-chosen invariant `J`), the hashing half
  (`Digest.update_absorbs`, VERIFIED), `KeepsJ J` (`sha_update` keeps `J`) and `EofStep`
  (a zero-length read goes to the padding; `ReadEof.eofStep`, VERIFIED).
* `sysTotalOn_of_loop` / `sysTotalOn_of_parts5`: the startup, the read loop and the tail
  (final, format, exit, with parametric cut points) give `SysTotalOn`.

Status: everything proved in this file is VERIFIED (no `sorry`, no new axiom); the missing
segments are hypotheses, not axioms.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.X86Sys (XState)
open Silmaril.Apps.Sha256sum.Binary.Digest (Loop AfterRead AtHead AtPad)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-! ## The cut point after a `read` -/

/-- `read` has just returned `chunk` at `0x402f06`; the struct holds `consumed`. -/
def ReturnedCut (e : Loop) (consumed chunk : List Byte) : Cut := fun _ message g h =>
  Ok message g h ∧ Loaded g.x.memory Apps.Sha256sum.Binary.Digest.base
    Apps.Sha256sum.Binary.Digest.code ∧ AfterRead e consumed chunk g.x

/-! ## Silent segments (VERIFIED) -/

/-- **A silent segment**: if from every state at `Pre` (where `Ok` holds) a run of retiring
steps reaches a state at `Post` with the same history, then `Seg domain Pre Post`. For the
segments between two system calls (`sha_final`, the hex formatting), proved over
`X86Sys.Isa.sys8` / `retStep` and transferred here with any `r11`. -/
theorem seg_of_reaches {domain : List Byte → Prop} {Pre Post : Cut}
    (h : ∀ (w : Apps.Sha256sum.World) (message : List Byte) (g : GS) (hist : List Ev),
      domain message → Pre w message g hist → Ok message g hist ∧
        ∃ t, Silmaril.Machine.Execution.Reaches retStep g.x t ∧
          Post w message { g with x := t } hist) :
    Seg domain Pre Post := by
  intro prog posix fs message g hist member pre
  obtain ⟨ok, t, run, post⟩ := h _ message g hist member pre
  exact leads_of_reaches run ok.1 ok post

/-- The same with the run over `X86Sys.rStep8` (the retiring steps of the `Ext8` machine,
`Isa.sys8`). -/
theorem seg_of_reaches8 {domain : List Byte → Prop} {Pre Post : Cut}
    (h : ∀ (w : Apps.Sha256sum.World) (message : List Byte) (g : GS) (hist : List Ev),
      domain message → Pre w message g hist → Ok message g hist ∧
        ∃ t, Silmaril.Machine.Execution.Reaches Apps.Sha256sum.X86Sys.rStep8 g.x t ∧
          Post w message { g with x := t } hist) :
    Seg domain Pre Post :=
  seg_of_reaches h

/-! ## A loop of `read` calls (generic, VERIFIED)

A read loop is given by its head cut `Head e`, the cut `Ret e chunk` right after a `read`
returned `chunk`, and the exit cut `Pad`. If the call half reaches `Ret` having read exactly
`chunk`, a nonempty chunk is absorbed back to the head (no event), and an empty chunk leads to
`Pad`, then the loop leads from the head to `Pad`: the number of message bytes not yet read
decreases at each nonempty read. -/

theorem loop_of_iter {domain : List Byte → Prop} {Head : Loop → Cut}
    {Ret : Loop → List Byte → Cut} {Pad : Cut}
    (call : ∀ (e : Loop) (prog : List Byte) (posix : Bool)
      (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult) (message : List Byte) (g : GS)
      (h : List Ev), domain message → Head e (world [prog] posix fs message) message g h →
        Leads (GStep (world [prog] posix fs message)) (Ok message)
          (fun g' h' => ∃ chunk, stdinRead h' = stdinRead h ++ chunk ∧ Ok message g' h' ∧
            Ret e chunk (world [prog] posix fs message) message g' h') g h)
    (absorb : ∀ (e : Loop) (chunk : List Byte) (prog : List Byte) (posix : Bool)
      (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult) (message : List Byte) (g : GS)
      (h : List Ev), domain message → chunk ≠ [] →
        Ret e chunk (world [prog] posix fs message) message g h →
        Leads (GStep (world [prog] posix fs message)) (Ok message)
          (fun g' h' => h' = h ∧ Head e (world [prog] posix fs message) message g' h') g h)
    (eof : ∀ (e : Loop) (prog : List Byte) (posix : Bool)
      (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult) (message : List Byte) (g : GS)
      (h : List Ev), domain message → Ret e [] (world [prog] posix fs message) message g h →
        Leads (GStep (world [prog] posix fs message)) (Ok message)
          (Pad (world [prog] posix fs message) message) g h) :
    Seg domain (fun w message g h => ∃ e, Head e w message g h) Pad := by
  intro prog posix fs message g h member ⟨e, head⟩
  suffices key : ∀ (n : Nat) (e : Loop) (g : GS) (h : List Ev),
      message.length - (stdinRead h).length = n →
      Head e (world [prog] posix fs message) message g h →
        Leads (GStep (world [prog] posix fs message)) (Ok message)
          (Pad (world [prog] posix fs message) message) g h from
    key _ e g h rfl head
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e g h hn head
    refine (call e prog posix fs message g h member head).trans ?_
    rintro g' h' ⟨chunk, hread, ok', ret⟩
    by_cases hc : chunk = []
    · subst hc
      exact eof e prog posix fs message g' h' member ret
    · refine (absorb e chunk prog posix fs message g' h' member hc ret).trans ?_
      rintro g'' h'' ⟨rfl, head'⟩
      have lenPre := ok'.2.2.1.length_le
      have lenH : (stdinRead h'').length = (stdinRead h).length + chunk.length := by
        rw [hread, List.length_append]
      have pos : 0 < chunk.length := List.length_pos_of_ne_nil hc
      exact ih _ (by omega) e g'' h'' rfl head'

/-! ## The read loop of `digest_file` -/

/-- **The system-call half of a read-loop iteration** (hypothesis until the read-loop track
lands), for an extra invariant `J e` of the prover's choice (the descriptor `e.fd` is `0`,
the kernel's stdin is the rest of the message, …: `HeadCut` alone does not fix the
descriptor, so `J` is needed for the call to be allowed): from the loop head, every execution
keeps `Ok` and reaches `0x402f06` right after `read(0, iobuf, 32768)` returned some `chunk`,
which is exactly what this step added to `stdinRead`, with `J` kept. -/
def ReadCall (domain : List Byte → Prop) (J : Loop → Cut) : Prop :=
  ∀ (e : Loop) (prog : List Byte) (posix : Bool)
    (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult) (message : List Byte) (g : GS)
    (h : List Ev), domain message →
    HeadCut e (world [prog] posix fs message) message g h →
      J e (world [prog] posix fs message) message g h →
      Leads (GStep (world [prog] posix fs message)) (Ok message)
        (fun g' h' => ∃ chunk, stdinRead h' = stdinRead h ++ chunk ∧
          ReturnedCut e (stdinRead h) chunk (world [prog] posix fs message) message g' h' ∧
          J e (world [prog] posix fs message) message g' h') g h

/-- **The extra invariant survives the hashing half** (hypothesis): along the retiring run of
`sha_update` from `0x402f06` to the loop head or the padding, `J` is kept (the run changes
only the program state, and `sha_update` writes the `struct sha`, not the `fd` slot). -/
def KeepsJ (J : Loop → Cut) : Prop :=
  ∀ (e : Loop) (consumed chunk : List Byte) (w : Apps.Sha256sum.World) (message : List Byte)
    (g : GS) (h : List Ev) (t : XState),
    ReturnedCut e consumed chunk w message g h → J e w message g h →
    Silmaril.Machine.Execution.Reaches Apps.Sha256sum.X86Sys.rStep g.x t →
    (AtHead e (consumed ++ chunk) t ∨ AtPad e consumed t) → J e w message { g with x := t } h

/-- **The standard invariant of the read loop**: the loop reads descriptor `0`, which (with
`1` and `2`) is still the standard stream; the kernel's stdin is the rest of the message;
nothing has been written yet. It depends only on the kernel and the history, so `sha_update`
keeps it (`keepsJ_stdin`). -/
def StdinJ (e : Loop) : Cut := fun _ message g h =>
  e.fd = 0#64 ∧ g.k.fds 0 = some .stdin ∧ g.k.fds 1 = some .stdout ∧
    g.k.fds 2 = some .stderr ∧
    g.k.stdin = .bytes (toSpec (message.drop (stdinRead h).length)) ∧ out h = []

/-- `sha_update` keeps `StdinJ` (VERIFIED: it changes only the program state). -/
theorem keepsJ_stdin : KeepsJ StdinJ := fun _ _ _ _ _ _ _ _ _ j _ _ => j

/-- **A zero-length read goes to the padding** (`test %rax,%rax; js; mov; je 0x403034`), by
retiring steps (`ReadEof.eofStep`, VERIFIED). -/
def EofStep : Prop :=
  ∀ (e : Loop) (consumed : List Byte) (s : XState), s.faulted = false →
    Loaded s.memory Apps.Sha256sum.Binary.Digest.base Apps.Sha256sum.Binary.Digest.code →
    AfterRead e consumed [] s →
      ∃ t, Silmaril.Machine.Execution.Reaches Apps.Sha256sum.X86Sys.rStep s t ∧
        t.faulted = false ∧
        Loaded t.memory Apps.Sha256sum.Binary.Digest.base Apps.Sha256sum.Binary.Digest.code ∧
        AtPad e consumed t

/-- The loop head with the extra invariant. -/
def HeadJ (J : Loop → Cut) (e : Loop) : Cut := fun w message g h =>
  HeadCut e w message g h ∧ J e w message g h

/-- The padding with the extra invariant, for some loop frame. -/
def PadJ (J : Loop → Cut) : Cut := fun w message g h =>
  ∃ e, PadCut e w message g h ∧ J e w message g h

/-- **VERIFIED. The read loop of `digest_file`** from `ReadCall`, `KeepsJ` and `EofStep`:
from the loop head, every execution keeps `Ok` and reaches the padding with everything read
absorbed. -/
theorem readLoop {domain : List Byte → Prop} {J : Loop → Cut} (readCall : ReadCall domain J)
    (keep : KeepsJ J) (eof : EofStep) :
    Seg domain (fun w message g h => ∃ e, HeadJ J e w message g h) (PadJ J) := by
  refine loop_of_iter (Ret := fun e chunk w message g h =>
      ∃ consumed, stdinRead h = consumed ++ chunk ∧ ReturnedCut e consumed chunk w message g h ∧
        J e w message g h) ?_ ?_ ?_
  · intro e prog posix fs message g h member ⟨head, j⟩
    refine (readCall e prog posix fs message g h member head j).trans ?_
    rintro g' h' ⟨chunk, hread, ret, j'⟩
    exact .done ⟨chunk, hread, ret.1, stdinRead h, hread, ret, j'⟩
  · rintro e chunk prog posix fs message g h member hc ⟨consumed, hread, ⟨ok, hl, after⟩, j⟩
    obtain ⟨t, hrun, hlv', hl', hpost⟩ :=
      Apps.Sha256sum.Binary.Digest.update_absorbs ok.2.2.2.2.2 hl after
    have ok' : Ok message { g with x := t } h :=
      ⟨ok.1, ok.2.1, ok.2.2.1, ok.2.2.2.1, ok.2.2.2.2.1, hlv'⟩
    have j' := keep e consumed chunk _ message g h t ⟨ok, hl, after⟩ j hrun
      (hpost.imp (fun p => p.1) fun p => p.2)
    refine leads_of_reaches (Apps.Sha256sum.X86Sys.reaches_rStep8 hrun) ok.1 ok ?_
    rcases hpost with ⟨headT, _⟩ | ⟨hnil, _⟩
    · exact ⟨rfl, ⟨ok', hl', by rw [hread]; exact headT⟩, j'⟩
    · exact absurd hnil hc
  · rintro e prog posix fs message g h member ⟨consumed, hread, ⟨ok, hl, after⟩, j⟩
    obtain ⟨t, hrun, hlv', hl', pad⟩ := eof e consumed g.x ok.2.2.2.2.2 hl after
    have ok' : Ok message { g with x := t } h :=
      ⟨ok.1, ok.2.1, ok.2.2.1, ok.2.2.2.1, ok.2.2.2.2.1, hlv'⟩
    have j' := keep e consumed [] _ message g h t ⟨ok, hl, after⟩ j hrun
      (.inr (by simpa using pad))
    refine leads_of_reaches (Apps.Sha256sum.X86Sys.reaches_rStep8 hrun) ok.1 ok ?_
    refine ⟨e, ⟨ok', hl', ?_⟩, j'⟩
    rw [hread, List.append_nil]
    exact pad

/-! ## The middle statement from the segments -/

/-- **`SysTotalOn` from the startup, the read-loop hypotheses and the tail** (VERIFIED). -/
theorem sysTotalOn_of_loop {domain : List Byte → Prop} {J : Loop → Cut}
    (startup : Seg domain LaunchCut (fun w message g h => ∃ e, HeadJ J e w message g h))
    (readCall : ReadCall domain J) (keep : KeepsJ J) (eof : EofStep)
    (tail : Seg domain (PadJ J) DoneCut) : SysTotalOn domain :=
  sysTotalOn_of_seg (startup.trans ((readLoop readCall keep eof).trans tail))

/-- **`SysTotalOn` with the tail split** into the final (`sha_final`, padding to the digest),
format (the 68-byte record in `obuf`) and exit (`close(0)`, `out_flush`, `close(1)`,
`close(2)`, `exit_group(0)`) segments, for any choice of the two inner cut points (VERIFIED). -/
theorem sysTotalOn_of_parts5 {domain : List Byte → Prop} {J : Loop → Cut}
    {Digested Formatted : Cut}
    (startup : Seg domain LaunchCut (fun w message g h => ∃ e, HeadJ J e w message g h))
    (readCall : ReadCall domain J) (keep : KeepsJ J) (eof : EofStep)
    (final : Seg domain (PadJ J) Digested) (format : Seg domain Digested Formatted)
    (exit : Seg domain Formatted DoneCut) : SysTotalOn domain :=
  sysTotalOn_of_loop startup readCall keep eof (final.trans (format.trans exit))

end Silmaril.Process.LPS.Problems.GnuSha256sum
